%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VRWzhsBnXs

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 181 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  409 (1620 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('3',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ~ ( r1_xboole_0 @ X43 @ sk_A ) ) ),
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

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( r2_hidden @ ( sk_C_1 @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_A )
      | ~ ( r1_xboole_0 @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( r2_hidden @ X40 @ ( sk_C_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['8','15'])).

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
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X43: $i] :
      ~ ( r2_hidden @ X43 @ sk_A ) ),
    inference(demod,[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('27',plain,(
    ! [X43: $i] :
      ~ ( r2_hidden @ X43 @ sk_A ) ),
    inference(demod,[status(thm)],['3','23'])).

thf('28',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1 = sk_A ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( r2_hidden @ ( sk_C_1 @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X43: $i] :
      ~ ( r2_hidden @ X43 @ sk_A ) ),
    inference(demod,[status(thm)],['3','23'])).

thf('44',plain,(
    $false ),
    inference('sup-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VRWzhsBnXs
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 79 iterations in 0.056s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(d4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.51         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf(t12_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X41 : $i, X42 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.51         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(t1_mcart_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51             ( ![B:$i]:
% 0.20/0.51               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X43 : $i]: (~ (r2_hidden @ X43 @ sk_A) | ~ (r1_xboole_0 @ X43 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf(t7_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( r2_hidden @ A @ B ) & 
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X38 : $i, X39 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X38 @ X39) | (r2_hidden @ (sk_C_1 @ X39) @ X39))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X43 : $i]: (~ (r2_hidden @ X43 @ sk_A) | ~ (r1_xboole_0 @ X43 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X38 @ X39)
% 0.20/0.51          | ~ (r2_hidden @ X40 @ X39)
% 0.20/0.51          | ~ (r2_hidden @ X40 @ (sk_C_1 @ X39)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('condensation', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.20/0.51          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.20/0.51          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '13'])).
% 0.20/0.51  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.20/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.51  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.51          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.51          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.51  thf('24', plain, (![X43 : $i]: ~ (r2_hidden @ X43 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1)
% 0.20/0.51          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1)
% 0.20/0.51          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '24'])).
% 0.20/0.51  thf('27', plain, (![X43 : $i]: ~ (r2_hidden @ X43 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '23'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]: ((sk_A) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1) | ((X1) = (sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X38 : $i, X39 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X38 @ X39) | (r2_hidden @ (sk_C_1 @ X39) @ X39))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (sk_A)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf(t2_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X41 : $i, X42 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.51          | (r2_hidden @ X4 @ X1)
% 0.20/0.51          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X41 : $i, X42 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X4 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (sk_A)) | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '39'])).
% 0.20/0.51  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, (![X0 : $i]: (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ X0)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain, (![X43 : $i]: ~ (r2_hidden @ X43 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '23'])).
% 0.20/0.51  thf('44', plain, ($false), inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
