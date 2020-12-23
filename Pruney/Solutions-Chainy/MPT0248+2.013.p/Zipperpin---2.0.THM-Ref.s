%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CtpNX7nM0U

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 193 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  474 (2303 expanded)
%              Number of equality atoms :   97 ( 525 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('14',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','15','27'])).

thf('29',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('30',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('38',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_C
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('40',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','40','45'])).

thf('47',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('49',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','29','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CtpNX7nM0U
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 115 iterations in 0.042s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(t43_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.46          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.46          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.46          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.46             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.46             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.46             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.46  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(commutativity_k2_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.46  thf(l51_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X39 : $i, X40 : $i]:
% 0.21/0.46         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.21/0.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X39 : $i, X40 : $i]:
% 0.21/0.46         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.21/0.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(t7_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.21/0.46      inference('sup+', [status(thm)], ['0', '7'])).
% 0.21/0.46  thf(l3_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X36 : $i, X37 : $i]:
% 0.21/0.46         (((X37) = (k1_tarski @ X36))
% 0.21/0.46          | ((X37) = (k1_xboole_0))
% 0.21/0.46          | ~ (r1_tarski @ X37 @ (k1_tarski @ X36)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('split', [status(esa)], ['11'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['14'])).
% 0.21/0.46  thf('16', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.46  thf('18', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.46      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X36 : $i, X37 : $i]:
% 0.21/0.46         (((X37) = (k1_tarski @ X36))
% 0.21/0.46          | ((X37) = (k1_xboole_0))
% 0.21/0.46          | ~ (r1_tarski @ X37 @ (k1_tarski @ X36)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.46      inference('split', [status(esa)], ['11'])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.46         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.46  thf('28', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['13', '15', '27'])).
% 0.21/0.46  thf('29', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.46      inference('split', [status(esa)], ['21'])).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.46  thf('32', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C)))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C)))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      (((r1_tarski @ sk_C @ (k1_tarski @ sk_A)))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      (![X36 : $i, X37 : $i]:
% 0.21/0.46         (((X37) = (k1_tarski @ X36))
% 0.21/0.46          | ((X37) = (k1_xboole_0))
% 0.21/0.46          | ~ (r1_tarski @ X37 @ (k1_tarski @ X36)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.46  thf('38', plain,
% 0.21/0.46      (((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A))))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.46  thf('39', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.21/0.46  thf('40', plain,
% 0.21/0.46      ((((sk_C) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.21/0.46  thf(t22_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.46  thf('41', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.46  thf('42', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.46  thf('43', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.46      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.46  thf(t12_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.46  thf('44', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.46  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.46  thf('46', plain,
% 0.21/0.46      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('demod', [status(thm)], ['33', '40', '45'])).
% 0.21/0.46  thf('47', plain,
% 0.21/0.46      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['21'])).
% 0.21/0.46  thf('48', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.46  thf('49', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.21/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.46      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.46  thf('50', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.21/0.46  thf('51', plain,
% 0.21/0.46      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['21'])).
% 0.21/0.46  thf('52', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.21/0.46  thf('53', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['30', '52'])).
% 0.21/0.46  thf('54', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['10', '29', '53'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
