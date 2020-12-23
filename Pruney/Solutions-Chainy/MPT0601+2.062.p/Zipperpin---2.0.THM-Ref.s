%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FFASuGnHTm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:49 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 145 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  448 (1330 expanded)
%              Number of equality atoms :   27 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k11_relat_1 @ X14 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k1_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('7',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('13',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_D_1 @ X10 @ X8 ) ) @ X8 )
      | ( X9
       != ( k1_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_D_1 @ X10 @ X8 ) ) @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X13 ) @ X14 )
      | ( r2_hidden @ X13 @ ( k11_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('23',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','25'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k11_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['13'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['16','32','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['14','34'])).

thf('36',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('40',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['16','32'])).

thf('41',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FFASuGnHTm
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:26:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.47  % Solved by: fo/fo7.sh
% 0.18/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.47  % done 51 iterations in 0.033s
% 0.18/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.47  % SZS output start Refutation
% 0.18/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.18/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.47  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.18/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.18/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.18/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.47  thf(t3_xboole_0, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.18/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.18/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.18/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.18/0.47  thf('0', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.18/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.47  thf(t204_relat_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( v1_relat_1 @ C ) =>
% 0.18/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.18/0.47         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.18/0.47  thf('1', plain,
% 0.18/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X13 @ (k11_relat_1 @ X14 @ X15))
% 0.18/0.47          | (r2_hidden @ (k4_tarski @ X15 @ X13) @ X14)
% 0.18/0.47          | ~ (v1_relat_1 @ X14))),
% 0.18/0.47      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.18/0.47  thf('2', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         ((r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 0.18/0.47          | ~ (v1_relat_1 @ X1)
% 0.18/0.47          | (r2_hidden @ 
% 0.18/0.47             (k4_tarski @ X0 @ (sk_C @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.47  thf(d4_relat_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.18/0.47       ( ![C:$i]:
% 0.18/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.18/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.18/0.47  thf('3', plain,
% 0.18/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.18/0.47         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.18/0.47          | (r2_hidden @ X6 @ X9)
% 0.18/0.47          | ((X9) != (k1_relat_1 @ X8)))),
% 0.18/0.47      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.18/0.47  thf('4', plain,
% 0.18/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.47         ((r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.18/0.47          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.18/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.18/0.47  thf('5', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         (~ (v1_relat_1 @ X0)
% 0.18/0.47          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 0.18/0.47          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['2', '4'])).
% 0.18/0.47  thf(t7_xboole_0, axiom,
% 0.18/0.47    (![A:$i]:
% 0.18/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.18/0.47  thf('6', plain,
% 0.18/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.18/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.18/0.47  thf('7', plain,
% 0.18/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.18/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.18/0.47  thf('8', plain,
% 0.18/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X2 @ X0)
% 0.18/0.47          | ~ (r2_hidden @ X2 @ X3)
% 0.18/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.18/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.47  thf('9', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         (((X0) = (k1_xboole_0))
% 0.18/0.47          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.18/0.47          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.47  thf('10', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         (((X0) = (k1_xboole_0))
% 0.18/0.47          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.18/0.47          | ((X0) = (k1_xboole_0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['6', '9'])).
% 0.18/0.47  thf('11', plain,
% 0.18/0.47      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.18/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.18/0.47  thf('12', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.18/0.47          | ~ (v1_relat_1 @ X1)
% 0.18/0.47          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['5', '11'])).
% 0.18/0.47  thf(t205_relat_1, conjecture,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( v1_relat_1 @ B ) =>
% 0.18/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.18/0.47         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.18/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.47    (~( ![A:$i,B:$i]:
% 0.18/0.47        ( ( v1_relat_1 @ B ) =>
% 0.18/0.47          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.18/0.47            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.18/0.47    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.18/0.47  thf('13', plain,
% 0.18/0.47      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.18/0.47        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('14', plain,
% 0.18/0.47      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.18/0.47         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('split', [status(esa)], ['13'])).
% 0.18/0.47  thf('15', plain,
% 0.18/0.47      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.18/0.47        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('16', plain,
% 0.18/0.47      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.18/0.47       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.18/0.47      inference('split', [status(esa)], ['15'])).
% 0.18/0.47  thf('17', plain,
% 0.18/0.47      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.18/0.47         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.18/0.47      inference('split', [status(esa)], ['13'])).
% 0.18/0.47  thf('18', plain,
% 0.18/0.47      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('split', [status(esa)], ['15'])).
% 0.18/0.47  thf('19', plain,
% 0.18/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X10 @ X9)
% 0.18/0.47          | (r2_hidden @ (k4_tarski @ X10 @ (sk_D_1 @ X10 @ X8)) @ X8)
% 0.18/0.47          | ((X9) != (k1_relat_1 @ X8)))),
% 0.18/0.47      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.18/0.47  thf('20', plain,
% 0.18/0.47      (![X8 : $i, X10 : $i]:
% 0.18/0.47         ((r2_hidden @ (k4_tarski @ X10 @ (sk_D_1 @ X10 @ X8)) @ X8)
% 0.18/0.47          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X8)))),
% 0.18/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.18/0.47  thf('21', plain,
% 0.18/0.47      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('sup-', [status(thm)], ['18', '20'])).
% 0.18/0.47  thf('22', plain,
% 0.18/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.18/0.47         (~ (r2_hidden @ (k4_tarski @ X15 @ X13) @ X14)
% 0.18/0.47          | (r2_hidden @ X13 @ (k11_relat_1 @ X14 @ X15))
% 0.18/0.47          | ~ (v1_relat_1 @ X14))),
% 0.18/0.47      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.18/0.47  thf('23', plain,
% 0.18/0.47      (((~ (v1_relat_1 @ sk_B_1)
% 0.18/0.47         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.18/0.47            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.18/0.47  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('25', plain,
% 0.18/0.47      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.18/0.47  thf('26', plain,
% 0.18/0.47      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.18/0.47             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.18/0.47      inference('sup+', [status(thm)], ['17', '25'])).
% 0.18/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.18/0.47  thf('27', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.18/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.18/0.47  thf('28', plain,
% 0.18/0.47      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.18/0.47  thf('29', plain,
% 0.18/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X2 @ X0)
% 0.18/0.47          | ~ (r2_hidden @ X2 @ X3)
% 0.18/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.18/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.18/0.47  thf('30', plain,
% 0.18/0.47      ((![X0 : $i]:
% 0.18/0.47          (~ (r1_xboole_0 @ (k11_relat_1 @ sk_B_1 @ sk_A) @ X0)
% 0.18/0.47           | ~ (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ X0)))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.18/0.47  thf('31', plain,
% 0.18/0.47      ((~ (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ k1_xboole_0))
% 0.18/0.47         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.18/0.47      inference('sup-', [status(thm)], ['27', '30'])).
% 0.18/0.47  thf('32', plain,
% 0.18/0.47      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.18/0.47       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['26', '31'])).
% 0.18/0.47  thf('33', plain,
% 0.18/0.47      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.18/0.47       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.18/0.47      inference('split', [status(esa)], ['13'])).
% 0.18/0.47  thf('34', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.18/0.47      inference('sat_resolution*', [status(thm)], ['16', '32', '33'])).
% 0.18/0.47  thf('35', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.18/0.47      inference('simpl_trail', [status(thm)], ['14', '34'])).
% 0.18/0.47  thf('36', plain,
% 0.18/0.47      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.18/0.47        | ~ (v1_relat_1 @ sk_B_1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['12', '35'])).
% 0.18/0.47  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('38', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.18/0.47  thf('39', plain,
% 0.18/0.47      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.18/0.47         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.18/0.47      inference('split', [status(esa)], ['15'])).
% 0.18/0.47  thf('40', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.18/0.47      inference('sat_resolution*', [status(thm)], ['16', '32'])).
% 0.18/0.47  thf('41', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.18/0.47      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 0.18/0.47  thf('42', plain, ($false),
% 0.18/0.47      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.18/0.47  
% 0.18/0.47  % SZS output end Refutation
% 0.18/0.47  
% 0.18/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
