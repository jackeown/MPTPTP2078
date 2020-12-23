%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m14gp4oK4m

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:14 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 130 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  496 (1351 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t75_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t75_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('35',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ sk_A )
      | ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('49',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m14gp4oK4m
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:51:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 326 iterations in 0.138s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(t75_xboole_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.58          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.58             ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t75_xboole_1])).
% 0.40/0.58  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t3_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf(d4_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.58          | (r2_hidden @ X4 @ X2)
% 0.40/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.58          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '4'])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.58          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.40/0.58          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.40/0.58          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ X1 @ X0)
% 0.40/0.58          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.40/0.58          | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '15'])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.58          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.58          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.40/0.58          | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.40/0.58          | (r2_hidden @ X0 @ X3)
% 0.40/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.40/0.58          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.40/0.58          | (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['24', '28'])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.40/0.58          | (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '22'])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.40/0.58         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.40/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.40/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.40/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('eq_fact', [status(thm)], ['32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.40/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('eq_fact', [status(thm)], ['32'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.58          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.40/0.58          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k3_xboole_0 @ sk_A @ sk_B)
% 0.40/0.58           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.58          | (r2_hidden @ X4 @ X1)
% 0.40/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.40/0.58          | (r2_hidden @ X1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ sk_B @ sk_A)
% 0.40/0.58          | ~ (r1_xboole_0 @ sk_B @ X0)
% 0.40/0.58          | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.40/0.58  thf('47', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['23', '46'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.58  thf('49', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.58  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
