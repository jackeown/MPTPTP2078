%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M4zTla63Nx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:35 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 202 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  497 (2782 expanded)
%              Number of equality atoms :   86 ( 619 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ ( k1_tarski @ X33 ) )
      | ( X32
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,(
    ! [X33: $i] :
      ( r1_tarski @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('24',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('27',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('39',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('43',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','40','44'])).

thf('46',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['37','45'])).

thf('47',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('50',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['14','50'])).

thf('52',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['37','45'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M4zTla63Nx
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 431 iterations in 0.167s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.44/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.62  thf(d3_tarski, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      (![X1 : $i, X3 : $i]:
% 0.44/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.62  thf(d3_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.44/0.62       ( ![D:$i]:
% 0.44/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.62           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X4 @ X5)
% 0.44/0.62          | (r2_hidden @ X4 @ X6)
% 0.44/0.62          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.44/0.62         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.44/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((r1_tarski @ X0 @ X1)
% 0.44/0.62          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '2'])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X1 : $i, X3 : $i]:
% 0.44/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.44/0.62          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.44/0.62  thf(t43_zfmisc_1, conjecture,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.44/0.62          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.62          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.62          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.62        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.44/0.62             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.62             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.62             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.44/0.62  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(l3_zfmisc_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.44/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X31 : $i, X32 : $i]:
% 0.44/0.62         (((X32) = (k1_tarski @ X31))
% 0.44/0.62          | ((X32) = (k1_xboole_0))
% 0.44/0.62          | ~ (r1_tarski @ X32 @ (k1_tarski @ X31)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | ((X0) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.44/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '11'])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X32 : $i, X33 : $i]:
% 0.44/0.62         ((r1_tarski @ X32 @ (k1_tarski @ X33)) | ((X32) != (k1_tarski @ X33)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X33 : $i]: (r1_tarski @ (k1_tarski @ X33) @ (k1_tarski @ X33))),
% 0.44/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ (k1_tarski @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['15', '17'])).
% 0.44/0.62  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 0.44/0.62        (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf(t11_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.62         ((r1_tarski @ X10 @ X11)
% 0.44/0.62          | ~ (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.44/0.62      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.44/0.62  thf('22', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.44/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.62  thf('25', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.44/0.62         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.44/0.62         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['24', '27'])).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.62  thf('30', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.62  thf(t12_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i]:
% 0.44/0.62         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.44/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.62  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.44/0.62         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['29', '32'])).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.44/0.62         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['34'])).
% 0.44/0.62  thf('36', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.44/0.62         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.44/0.62      inference('split', [status(esa)], ['34'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('split', [status(esa)], ['39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.62      inference('split', [status(esa)], ['34'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      ((((sk_B) != (sk_B)))
% 0.44/0.62         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.44/0.62  thf('45', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['38', '40', '44'])).
% 0.44/0.62  thf('46', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['37', '45'])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['33', '46'])).
% 0.44/0.62  thf('48', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('split', [status(esa)], ['13'])).
% 0.44/0.62  thf('50', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.44/0.62  thf('51', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['14', '50'])).
% 0.44/0.62  thf('52', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['37', '45'])).
% 0.44/0.62  thf('53', plain, ($false),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['12', '51', '52'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
