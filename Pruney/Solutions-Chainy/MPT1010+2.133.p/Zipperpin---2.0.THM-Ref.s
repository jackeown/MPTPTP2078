%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ryc0A9wKQt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 123 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  374 (1427 expanded)
%              Number of equality atoms :   40 ( 108 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X34 @ X31 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X24 ) @ X28 ) )
      | ~ ( r2_hidden @ X26 @ X28 )
      | ( X25 != X24 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('16',plain,(
    ! [X24: $i,X26: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X28 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X24 ) @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_2 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_zfmisc_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_2 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_tarski @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_zfmisc_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 = X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X24 ) @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('33',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r2_hidden @ sk_B_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] : ( sk_B_1 = X0 ) ),
    inference(demod,[status(thm)],['30','34'])).

thf('36',plain,(
    sk_B_1 != sk_B_1 ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ryc0A9wKQt
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 145 iterations in 0.057s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(t65_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.48         ( m1_subset_1 @
% 0.21/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.48            ( m1_subset_1 @
% 0.21/0.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.48          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.48  thf('0', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_2) != (sk_B_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t7_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X31 @ X32)
% 0.21/0.48          | ((X33) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_funct_1 @ X34)
% 0.21/0.48          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.21/0.48          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.48          | (r2_hidden @ (k1_funct_1 @ X34 @ X31) @ X33))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.21/0.48          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.21/0.48          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.48          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.21/0.48          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_2) @ (k1_tarski @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.48          | ((X10) = (X7))
% 0.21/0.48          | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X7 : $i, X10 : $i]:
% 0.21/0.48         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.21/0.48        | ((k1_funct_1 @ sk_D_1 @ sk_C_2) = (sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.48  thf('12', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_2) != (sk_B_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t128_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @
% 0.21/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X25 @ X26) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ X24) @ X28))
% 0.21/0.48          | ~ (r2_hidden @ X26 @ X28)
% 0.21/0.48          | ((X25) != (X24)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X24 : $i, X26 : $i, X28 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X26 @ X28)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X24 @ X26) @ 
% 0.21/0.48             (k2_zfmisc_1 @ (k1_tarski @ X24) @ X28)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (r2_hidden @ (k4_tarski @ X0 @ sk_C_2) @ 
% 0.21/0.48          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_2) @ 
% 0.21/0.48        (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['13', '17'])).
% 0.21/0.48  thf(t113_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X22 @ X23) = (k1_xboole_0))
% 0.21/0.48          | ((X22) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X23 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.48  thf('21', plain, ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_2) @ k1_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['18', '20'])).
% 0.21/0.48  thf('22', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X7 : $i, X10 : $i]:
% 0.21/0.48         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, (((k4_tarski @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X22 @ X23) = (k1_xboole_0))
% 0.21/0.48          | ((X23) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X22 : $i]: ((k2_zfmisc_1 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.48         (((X25) = (X24))
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X25 @ X26) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ X24) @ X27)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0) | ((X2) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i]: (~ (r2_hidden @ sk_B_1 @ k1_xboole_0) | ((sk_B_1) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '29'])).
% 0.21/0.48  thf('31', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('33', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('34', plain, ((r2_hidden @ sk_B_1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['31', '33'])).
% 0.21/0.48  thf('35', plain, (![X0 : $i]: ((sk_B_1) = (X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '34'])).
% 0.21/0.48  thf('36', plain, (((sk_B_1) != (sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.48  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
