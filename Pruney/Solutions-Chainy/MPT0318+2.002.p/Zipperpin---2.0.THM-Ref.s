%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uz3LV9lD7n

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 530 expanded)
%              Number of leaves         :   18 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  487 (5117 expanded)
%              Number of equality atoms :   81 ( 996 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X33 )
      | ( X33
       != ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('7',plain,(
    ~ ( r2_hidden @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('8',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X38 @ X37 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('16',plain,(
    ! [X40: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('17',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('18',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X38 @ X37 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X40: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('29',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('34',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('36',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('38',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','41'])).

thf('43',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('44',plain,(
    ! [X40: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('45',plain,(
    ! [X36: $i] :
      ( r1_tarski @ X36 @ ( k1_zfmisc_1 @ ( k3_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('49',plain,(
    r2_hidden @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','40'])).

thf('51',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','40'])).

thf('52',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('53',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','40'])).

thf('54',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['42','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uz3LV9lD7n
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 66 iterations in 0.022s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(t1_zfmisc_1, axiom,
% 0.20/0.46    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.20/0.46  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.46  thf('1', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.46  thf(d1_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X31 @ X32)
% 0.20/0.46          | (r2_hidden @ X31 @ X33)
% 0.20/0.46          | ((X33) != (k1_zfmisc_1 @ X32)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X31 : $i, X32 : $i]:
% 0.20/0.46         ((r2_hidden @ X31 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X31 @ X32))),
% 0.20/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.46  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.46  thf('5', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.46  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.46  thf('7', plain, (~ (r2_hidden @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf(t130_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.46       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.46          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.20/0.46        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf(t113_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X37 : $i, X38 : $i]:
% 0.20/0.46         (((X37) = (k1_xboole_0))
% 0.20/0.46          | ((X38) = (k1_xboole_0))
% 0.20/0.46          | ((k2_zfmisc_1 @ X38 @ X37) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46         | ((sk_A) = (k1_xboole_0))
% 0.20/0.46         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.46  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf(t31_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.46  thf('16', plain, (![X40 : $i]: ((k3_tarski @ (k1_tarski @ X40)) = (X40))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((((k3_tarski @ k1_xboole_0) = (sk_B)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.46  thf('18', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X37 : $i, X38 : $i]:
% 0.20/0.46         (((X37) = (k1_xboole_0))
% 0.20/0.46          | ((X38) = (k1_xboole_0))
% 0.20/0.46          | ((k2_zfmisc_1 @ X38 @ X37) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.46         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.46  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('28', plain, (![X40 : $i]: ((k3_tarski @ (k1_tarski @ X40)) = (X40))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      ((((k3_tarski @ k1_xboole_0) = (sk_B)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.46  thf('30', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('demod', [status(thm)], ['26', '31'])).
% 0.20/0.46  thf('33', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      ((~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0))
% 0.20/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.20/0.46       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('split', [status(esa)], ['8'])).
% 0.20/0.46  thf('40', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.20/0.46  thf('41', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['20', '40'])).
% 0.20/0.46  thf('42', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['7', '41'])).
% 0.20/0.46  thf('43', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.46  thf('44', plain, (![X40 : $i]: ((k3_tarski @ (k1_tarski @ X40)) = (X40))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.46  thf(t100_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.46  thf('45', plain,
% 0.20/0.46      (![X36 : $i]: (r1_tarski @ X36 @ (k1_zfmisc_1 @ (k3_tarski @ X36)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.46  thf('46', plain,
% 0.20/0.46      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.46  thf('47', plain,
% 0.20/0.46      ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['43', '46'])).
% 0.20/0.46  thf('48', plain,
% 0.20/0.46      (![X31 : $i, X32 : $i]:
% 0.20/0.46         ((r2_hidden @ X31 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X31 @ X32))),
% 0.20/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.46  thf('49', plain,
% 0.20/0.46      ((r2_hidden @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.46  thf('50', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['20', '40'])).
% 0.20/0.46  thf('51', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['20', '40'])).
% 0.20/0.46  thf('52', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.46  thf('53', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['20', '40'])).
% 0.20/0.46  thf('54', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.46  thf('55', plain, ($false), inference('demod', [status(thm)], ['42', '54'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
