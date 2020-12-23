%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ydF9zyTAch

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  75 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  470 ( 938 expanded)
%              Number of equality atoms :   67 ( 129 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k20_mcart_1_type,type,(
    k20_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k19_mcart_1_type,type,(
    k19_mcart_1: $i > $i )).

thf(k17_mcart_1_type,type,(
    k17_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k18_mcart_1_type,type,(
    k18_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d17_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k20_mcart_1 @ A )
      = ( k2_mcart_1 @ ( k2_mcart_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k20_mcart_1 @ X3 )
      = ( k2_mcart_1 @ ( k2_mcart_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d17_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k20_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = ( k2_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t89_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k20_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
        = E )
      & ( ( k19_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
        = D )
      & ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
        = B )
      & ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k20_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
          = E )
        & ( ( k19_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) )
          = D )
        & ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
          = B )
        & ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t89_mcart_1])).

thf('3',plain,
    ( ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_B )
    | ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_A )
    | ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_D )
    | ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_D @ sk_E ) )
     != sk_E )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( sk_E != sk_E )
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( $false
   <= ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d15_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k18_mcart_1 @ A )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ( k18_mcart_1 @ X1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d15_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k18_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = ( k2_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_B )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('15',plain,
    ( ( sk_B != sk_B )
   <= ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = sk_B ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d14_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k17_mcart_1 @ A )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k17_mcart_1 @ X0 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d14_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k17_mcart_1 @ ( k4_tarski @ X0 @ X1 ) )
      = ( k1_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_A )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('23',plain,
    ( ( sk_A != sk_A )
   <= ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X4 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d16_mcart_1,axiom,(
    ! [A: $i] :
      ( ( k19_mcart_1 @ A )
      = ( k1_mcart_1 @ ( k2_mcart_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k19_mcart_1 @ X2 )
      = ( k1_mcart_1 @ ( k2_mcart_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d16_mcart_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k19_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = ( k1_mcart_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_D )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_D @ sk_E ) )
     != sk_D )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('31',plain,
    ( ( sk_D != sk_D )
   <= ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
    = sk_D ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_E )
    | ( ( k19_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
     != sk_D )
    | ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_A )
    | ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
     != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,(
    ( k20_mcart_1 @ ( k4_tarski @ sk_F @ ( k4_tarski @ sk_D @ sk_E ) ) )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['16','24','32','33'])).

thf('35',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['8','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ydF9zyTAch
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 22 iterations in 0.010s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.45  thf(k20_mcart_1_type, type, k20_mcart_1: $i > $i).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.45  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.45  thf(k19_mcart_1_type, type, k19_mcart_1: $i > $i).
% 0.20/0.45  thf(k17_mcart_1_type, type, k17_mcart_1: $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.45  thf(k18_mcart_1_type, type, k18_mcart_1: $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.45  thf(t7_mcart_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.45       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X4 : $i, X6 : $i]: ((k2_mcart_1 @ (k4_tarski @ X4 @ X6)) = (X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.45  thf(d17_mcart_1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k20_mcart_1 @ A ) = ( k2_mcart_1 @ ( k2_mcart_1 @ A ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X3 : $i]: ((k20_mcart_1 @ X3) = (k2_mcart_1 @ (k2_mcart_1 @ X3)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d17_mcart_1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k20_mcart_1 @ (k4_tarski @ X1 @ X0)) = (k2_mcart_1 @ X0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t89_mcart_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.45     ( ( ( k20_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) ) = ( E ) ) & 
% 0.20/0.45       ( ( k19_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) ) = ( D ) ) & 
% 0.20/0.45       ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) = ( B ) ) & 
% 0.20/0.45       ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) = ( A ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.45        ( ( ( k20_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) ) = ( E ) ) & 
% 0.20/0.46          ( ( k19_mcart_1 @ ( k4_tarski @ F @ ( k4_tarski @ D @ E ) ) ) = ( D ) ) & 
% 0.20/0.46          ( ( k18_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) = ( B ) ) & 
% 0.20/0.46          ( ( k17_mcart_1 @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) = ( A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t89_mcart_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          != (sk_B))
% 0.20/0.46        | ((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46            != (sk_A))
% 0.20/0.46        | ((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46            != (sk_D))
% 0.20/0.46        | ((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46            != (sk_E)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46          != (sk_E)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_E))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((((k2_mcart_1 @ (k4_tarski @ sk_D @ sk_E)) != (sk_E)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_E))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]: ((k2_mcart_1 @ (k4_tarski @ X4 @ X6)) = (X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((((sk_E) != (sk_E)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_E))))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (($false)
% 0.20/0.46         <= (~
% 0.20/0.46             (((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_E))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]: ((k1_mcart_1 @ (k4_tarski @ X4 @ X5)) = (X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf(d15_mcart_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k18_mcart_1 @ A ) = ( k2_mcart_1 @ ( k1_mcart_1 @ A ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X1 : $i]: ((k18_mcart_1 @ X1) = (k2_mcart_1 @ (k1_mcart_1 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d15_mcart_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k18_mcart_1 @ (k4_tarski @ X0 @ X1)) = (k2_mcart_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      ((((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          != (sk_B)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46                = (sk_B))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) != (sk_B)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46                = (sk_B))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]: ((k2_mcart_1 @ (k4_tarski @ X4 @ X6)) = (X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((sk_B) != (sk_B)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46                = (sk_B))))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          = (sk_B)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]: ((k1_mcart_1 @ (k4_tarski @ X4 @ X5)) = (X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf(d14_mcart_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k17_mcart_1 @ A ) = ( k1_mcart_1 @ ( k1_mcart_1 @ A ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X0 : $i]: ((k17_mcart_1 @ X0) = (k1_mcart_1 @ (k1_mcart_1 @ X0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d14_mcart_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k17_mcart_1 @ (k4_tarski @ X0 @ X1)) = (k1_mcart_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      ((((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          != (sk_A)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46                = (sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      ((((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) != (sk_A)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46                = (sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]: ((k1_mcart_1 @ (k4_tarski @ X4 @ X5)) = (X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((((sk_A) != (sk_A)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46                = (sk_A))))),
% 0.20/0.46      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          = (sk_A)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]: ((k2_mcart_1 @ (k4_tarski @ X4 @ X6)) = (X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf(d16_mcart_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k19_mcart_1 @ A ) = ( k1_mcart_1 @ ( k2_mcart_1 @ A ) ) ))).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X2 : $i]: ((k19_mcart_1 @ X2) = (k1_mcart_1 @ (k2_mcart_1 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d16_mcart_1])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k19_mcart_1 @ (k4_tarski @ X1 @ X0)) = (k1_mcart_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      ((((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46          != (sk_D)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_D))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      ((((k1_mcart_1 @ (k4_tarski @ sk_D @ sk_E)) != (sk_D)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_D))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]: ((k1_mcart_1 @ (k4_tarski @ X4 @ X5)) = (X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      ((((sk_D) != (sk_D)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46                = (sk_D))))),
% 0.20/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      ((((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46          = (sk_D)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46          = (sk_E))) | 
% 0.20/0.46       ~
% 0.20/0.46       (((k19_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46          = (sk_D))) | 
% 0.20/0.46       ~
% 0.20/0.46       (((k17_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          = (sk_A))) | 
% 0.20/0.46       ~
% 0.20/0.46       (((k18_mcart_1 @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46          = (sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k20_mcart_1 @ (k4_tarski @ sk_F @ (k4_tarski @ sk_D @ sk_E)))
% 0.20/0.46          = (sk_E)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['16', '24', '32', '33'])).
% 0.20/0.46  thf('35', plain, ($false),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['8', '34'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
