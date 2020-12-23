%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8izN8yNdhP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 171 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  539 (1840 expanded)
%              Number of equality atoms :   31 ( 119 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) )
        = ( k1_tarski @ X24 ) )
      | ( X24 = X25 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('25',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','8','19','24'])).

thf('26',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['23','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X30 ) ) )
      | ( X28 != X30 )
      | ( X27 != X26 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('29',plain,(
    ! [X26: $i,X30: $i] :
      ( r2_hidden @ ( k4_tarski @ X26 @ X30 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','8','19','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','39'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['27','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8izN8yNdhP
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:15:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 152 iterations in 0.079s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.56  thf(t129_zfmisc_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( r2_hidden @
% 0.22/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.56       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56        ( ( r2_hidden @
% 0.22/0.56            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.56          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      ((((sk_B) != (sk_D))
% 0.22/0.56        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.22/0.56        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56             (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56           (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (~
% 0.22/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))) | 
% 0.22/0.56       ~ (((sk_B) = (sk_D))) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_C_1)
% 0.22/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56           (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))
% 0.22/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('split', [status(esa)], ['3'])).
% 0.22/0.56  thf(l54_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.56         ((r2_hidden @ X10 @ X11)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.22/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_C_1))
% 0.22/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.22/0.56       ~
% 0.22/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))
% 0.22/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('split', [status(esa)], ['3'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.56         ((r2_hidden @ X12 @ X13)
% 0.22/0.56          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.22/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.22/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.56  thf(t20_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.56         ( k1_tarski @ A ) ) <=>
% 0.22/0.56       ( ( A ) != ( B ) ) ))).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X24 : $i, X25 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25))
% 0.22/0.56            = (k1_tarski @ X24))
% 0.22/0.56          | ((X24) = (X25)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.56  thf(l33_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.56       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X7 : $i, X8 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X7 @ X8)
% 0.22/0.56          | ((k4_xboole_0 @ (k1_tarski @ X7) @ X8) != (k1_tarski @ X7)))),
% 0.22/0.56      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.22/0.56          | ((X0) = (X1))
% 0.22/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      ((((sk_B) = (sk_D)))
% 0.22/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '15'])).
% 0.22/0.56  thf('17', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      ((((sk_B) != (sk_B)))
% 0.22/0.56         <= (~ (((sk_B) = (sk_D))) & 
% 0.22/0.56             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      ((((sk_B) = (sk_D))) | 
% 0.22/0.56       ~
% 0.22/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (~
% 0.22/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['2', '8', '19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56          (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      ((((sk_B) = (sk_D))
% 0.22/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56           (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('23', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.22/0.56      inference('split', [status(esa)], ['22'])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      ((((sk_B) = (sk_D))) | 
% 0.22/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('split', [status(esa)], ['22'])).
% 0.22/0.56  thf('25', plain, ((((sk_B) = (sk_D)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['2', '8', '19', '24'])).
% 0.22/0.56  thf('26', plain, (((sk_B) = (sk_D))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['23', '25'])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56          (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_B)))),
% 0.22/0.56      inference('demod', [status(thm)], ['21', '26'])).
% 0.22/0.56  thf(t34_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( r2_hidden @
% 0.22/0.56         ( k4_tarski @ A @ B ) @ 
% 0.22/0.56         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.56       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.22/0.56         ((r2_hidden @ (k4_tarski @ X27 @ X28) @ 
% 0.22/0.56           (k2_zfmisc_1 @ (k1_tarski @ X26) @ (k1_tarski @ X30)))
% 0.22/0.56          | ((X28) != (X30))
% 0.22/0.56          | ((X27) != (X26)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (![X26 : $i, X30 : $i]:
% 0.22/0.56         (r2_hidden @ (k4_tarski @ X26 @ X30) @ 
% 0.22/0.56          (k2_zfmisc_1 @ (k1_tarski @ X26) @ (k1_tarski @ X30)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.22/0.56      inference('split', [status(esa)], ['3'])).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.22/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.56         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.22/0.56      inference('split', [status(esa)], ['3'])).
% 0.22/0.56  thf('32', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['2', '8', '19', '31'])).
% 0.22/0.56  thf('33', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.22/0.56  thf(d3_tarski, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (![X1 : $i, X3 : $i]:
% 0.22/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X1 : $i, X3 : $i]:
% 0.22/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.56          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.56          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.56      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.56  thf('40', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)),
% 0.22/0.56      inference('sup-', [status(thm)], ['33', '39'])).
% 0.22/0.56  thf(t118_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.56       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.22/0.56         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X20 @ X21)
% 0.22/0.56          | (r1_tarski @ (k2_zfmisc_1 @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.22/0.56          (k2_zfmisc_1 @ sk_C_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.56          | (r2_hidden @ X0 @ X2)
% 0.22/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((r2_hidden @ X1 @ (k2_zfmisc_1 @ sk_C_1 @ X0))
% 0.22/0.56          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.56  thf('45', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.22/0.56          (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['29', '44'])).
% 0.22/0.56  thf('46', plain, ($false), inference('demod', [status(thm)], ['27', '45'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
