%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KiqnFCWngE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:34 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 112 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 (1310 expanded)
%              Number of equality atoms :   38 (  95 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X48 @ X45 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X40 != X39 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X39 ) )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X39: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X39 ) )
     != ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('17',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('18',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KiqnFCWngE
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:42:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 199 iterations in 0.109s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.57  thf(t65_funct_2, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.39/0.57       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.39/0.57            ( m1_subset_1 @
% 0.39/0.57              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.39/0.57          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.39/0.57  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t7_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57       ( ( r2_hidden @ C @ A ) =>
% 0.39/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X45 @ X46)
% 0.39/0.57          | ((X47) = (k1_xboole_0))
% 0.39/0.57          | ~ (v1_funct_1 @ X48)
% 0.39/0.57          | ~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.39/0.57          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.39/0.57          | (r2_hidden @ (k1_funct_1 @ X48 @ X45) @ X47))),
% 0.39/0.57      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D_1)
% 0.39/0.57          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.39/0.57          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.39/0.57        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '6'])).
% 0.39/0.57  thf(d1_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X6 : $i, X9 : $i]:
% 0.39/0.57         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.39/0.57        | ((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '9'])).
% 0.39/0.57  thf('11', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('12', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf(t20_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.57         ( k1_tarski @ A ) ) <=>
% 0.39/0.57       ( ( A ) != ( B ) ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X39 : $i, X40 : $i]:
% 0.39/0.57         (((X40) != (X39))
% 0.39/0.57          | ((k4_xboole_0 @ (k1_tarski @ X40) @ (k1_tarski @ X39))
% 0.39/0.57              != (k1_tarski @ X40)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X39 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X39))
% 0.39/0.57           != (k1_tarski @ X39))),
% 0.39/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0)
% 0.39/0.57         != (k1_tarski @ sk_B_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '14'])).
% 0.39/0.57  thf('16', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('17', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.39/0.57  thf(t9_mcart_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.39/0.57                 ( ![C:$i,D:$i]:
% 0.39/0.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.39/0.57                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X42 : $i]:
% 0.39/0.57         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.39/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.39/0.57  thf(d5_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.57          | (r2_hidden @ X4 @ X1)
% 0.39/0.57          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.57         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.57          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X42 : $i]:
% 0.39/0.57         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.39/0.57      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.57          | ~ (r2_hidden @ X4 @ X2)
% 0.39/0.57          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.39/0.57          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.57          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.39/0.57          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '26'])).
% 0.39/0.57  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.57  thf('29', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '28'])).
% 0.39/0.57  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
