%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlXztggZSR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 124 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  399 (1411 expanded)
%              Number of equality atoms :   45 ( 117 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X47 @ X44 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ( X11 = X10 )
      | ( X11 = X7 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('16',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42 != X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) )
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('17',plain,(
    ! [X41: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X41 ) )
     != ( k1_tarski @ X41 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('20',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('21',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlXztggZSR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 297 iterations in 0.109s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(t65_funct_2, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.56         ( m1_subset_1 @
% 0.20/0.56           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.56       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.56            ( m1_subset_1 @
% 0.20/0.56              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.56          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.56  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t7_funct_2, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X44 @ X45)
% 0.20/0.56          | ((X46) = (k1_xboole_0))
% 0.20/0.56          | ~ (v1_funct_1 @ X47)
% 0.20/0.56          | ~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.20/0.56          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.20/0.56          | (r2_hidden @ (k1_funct_1 @ X47 @ X44) @ X46))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k1_tarski @ sk_B_1))
% 0.20/0.56          | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.20/0.56          | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.56          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('5', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k1_tarski @ sk_B_1))
% 0.20/0.56          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.20/0.56        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C) @ (k1_tarski @ sk_B_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('8', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(d2_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X7 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X11 @ X9)
% 0.20/0.56          | ((X11) = (X10))
% 0.20/0.56          | ((X11) = (X7))
% 0.20/0.56          | ((X9) != (k2_tarski @ X10 @ X7)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X7 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (((X11) = (X7))
% 0.20/0.56          | ((X11) = (X10))
% 0.20/0.56          | ~ (r2_hidden @ X11 @ (k2_tarski @ X10 @ X7)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.20/0.56        | ((k1_funct_1 @ sk_D_2 @ sk_C) = (sk_B_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.56  thf('14', plain, (((k1_funct_1 @ sk_D_2 @ sk_C) != (sk_B_1))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf(t20_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.56         ( k1_tarski @ A ) ) <=>
% 0.20/0.56       ( ( A ) != ( B ) ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X41 : $i, X42 : $i]:
% 0.20/0.56         (((X42) != (X41))
% 0.20/0.56          | ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X41))
% 0.20/0.56              != (k1_tarski @ X42)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X41 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X41))
% 0.20/0.56           != (k1_tarski @ X41))),
% 0.20/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0)
% 0.20/0.56         != (k1_tarski @ sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.56  thf('19', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('20', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.56  thf(t7_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.56  thf(d5_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | (r2_hidden @ X4 @ X1)
% 0.20/0.56          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.56          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.56          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.56          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.20/0.56          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '29'])).
% 0.20/0.56  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.56  thf('32', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['21', '31'])).
% 0.20/0.56  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
