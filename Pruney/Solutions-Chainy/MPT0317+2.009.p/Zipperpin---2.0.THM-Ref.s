%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dRlYlzPJ3N

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 187 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  519 (1959 expanded)
%              Number of equality atoms :   35 ( 146 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t129_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
    | ( sk_B != sk_D_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X26: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_B = sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = sk_D_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B = sk_D_1 )
   <= ( sk_B = sk_D_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('28',plain,(
    sk_B = sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['2','8','22','27'])).

thf('29',plain,(
    sk_B = sk_D_1 ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('33',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_A ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','8','22','41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['30','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dRlYlzPJ3N
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 97 iterations in 0.041s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.49  thf(t129_zfmisc_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( r2_hidden @
% 0.19/0.49         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.19/0.49       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49        ( ( r2_hidden @
% 0.19/0.49            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.19/0.49          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((((sk_B) != (sk_D_1))
% 0.19/0.49        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.19/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))) | 
% 0.19/0.49       ~ (((sk_B) = (sk_D_1))) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C)
% 0.19/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf(l54_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.19/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.49         ((r2_hidden @ X27 @ X28)
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X30)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.49         ((r2_hidden @ X29 @ X30)
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X30)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf(t76_enumset1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X26 : $i]: ((k1_enumset1 @ X26 @ X26 @ X26) = (k1_tarski @ X26))),
% 0.19/0.49      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.19/0.49  thf(t70_enumset1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.19/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf(d2_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.49          | ((X4) = (X3))
% 0.19/0.49          | ((X4) = (X0))
% 0.19/0.49          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         (((X4) = (X0))
% 0.19/0.49          | ((X4) = (X3))
% 0.19/0.49          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((((sk_B) = (sk_D_1)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '18'])).
% 0.19/0.49  thf('20', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((((sk_B) != (sk_B)))
% 0.19/0.49         <= (~ (((sk_B) = (sk_D_1))) & 
% 0.19/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((sk_B) = (sk_D_1))) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '22'])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1)))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((sk_B) = (sk_D_1))
% 0.19/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain, ((((sk_B) = (sk_D_1))) <= ((((sk_B) = (sk_D_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((((sk_B) = (sk_D_1))) | 
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['25'])).
% 0.19/0.49  thf('28', plain, ((((sk_B) = (sk_D_1)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '22', '27'])).
% 0.19/0.49  thf('29', plain, (((sk_B) = (sk_D_1))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.19/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.49         (((X1) != (X0))
% 0.19/0.49          | (r2_hidden @ X1 @ X2)
% 0.19/0.49          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.49  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['31', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.19/0.49         ((r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X31))
% 0.19/0.49          | ~ (r2_hidden @ X29 @ X31)
% 0.19/0.49          | ~ (r2_hidden @ X27 @ X28))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((![X0 : $i, X1 : $i]:
% 0.19/0.49          (~ (r2_hidden @ X1 @ X0)
% 0.19/0.49           | (r2_hidden @ (k4_tarski @ X1 @ sk_A) @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.19/0.49         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 0.19/0.49           (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C)))
% 0.19/0.49         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.49         ((r2_hidden @ X29 @ X30)
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X30)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf('42', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '22', '41'])).
% 0.19/0.49  thf('43', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.19/0.49  thf('44', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['31', '33'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.19/0.49         ((r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X31))
% 0.19/0.49          | ~ (r2_hidden @ X29 @ X31)
% 0.19/0.49          | ~ (r2_hidden @ X27 @ X28))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.19/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.19/0.49          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '46'])).
% 0.19/0.49  thf('48', plain, ($false), inference('demod', [status(thm)], ['30', '47'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
