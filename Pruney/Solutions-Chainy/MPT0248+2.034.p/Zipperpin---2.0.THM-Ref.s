%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t8z2sAmAcK

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 133 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  373 (1615 expanded)
%              Number of equality atoms :   80 ( 382 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('10',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','11','23'])).

thf('25',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','24'])).

thf('26',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','24'])).

thf('39',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('41',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['26','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','25','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t8z2sAmAcK
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 76 iterations in 0.043s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(t43_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.51          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.51          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.51          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.51             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.51             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.51             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.20/0.51  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.51  thf(t7_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf(l3_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (((X14) = (k1_tarski @ X13))
% 0.20/0.51          | ((X14) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X14 @ (k1_tarski @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.51  thf('6', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['10'])).
% 0.20/0.51  thf('12', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.51  thf('14', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (((X14) = (k1_tarski @ X13))
% 0.20/0.51          | ((X14) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X14 @ (k1_tarski @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((((sk_B) != (sk_B)))
% 0.20/0.51         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf('24', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['9', '11', '23'])).
% 0.20/0.51  thf('25', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['8', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('27', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf(t3_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('29', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf(t40_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X4)
% 0.20/0.51           = (k4_xboole_0 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.51  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.20/0.51         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['28', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['27', '36'])).
% 0.20/0.51  thf('38', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['8', '24'])).
% 0.20/0.51  thf('39', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('41', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['26', '41'])).
% 0.20/0.51  thf('43', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['6', '25', '42'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
