%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YmXuuFVnhE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:29 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   58 (  66 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  393 ( 569 expanded)
%              Number of equality atoms :   38 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X52 @ X49 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('9',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X46: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X46 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['7','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YmXuuFVnhE
% 0.17/0.38  % Computer   : n008.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 12:00:15 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.46  % Solved by: fo/fo7.sh
% 0.24/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.46  % done 43 iterations in 0.015s
% 0.24/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.46  % SZS output start Refutation
% 0.24/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.24/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.46  thf(d1_enumset1, axiom,
% 0.24/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.46     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.46       ( ![E:$i]:
% 0.24/0.46         ( ( r2_hidden @ E @ D ) <=>
% 0.24/0.46           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.24/0.46  thf(zf_stmt_0, axiom,
% 0.24/0.46    (![E:$i,C:$i,B:$i,A:$i]:
% 0.24/0.46     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.24/0.46       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.24/0.46  thf('0', plain,
% 0.24/0.46      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.46         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.24/0.46          | ((X7) = (X8))
% 0.24/0.46          | ((X7) = (X9))
% 0.24/0.46          | ((X7) = (X10)))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.46  thf(t65_funct_2, conjecture,
% 0.24/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.24/0.46         ( m1_subset_1 @
% 0.24/0.46           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.24/0.46       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.24/0.46  thf(zf_stmt_1, negated_conjecture,
% 0.24/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.24/0.46            ( m1_subset_1 @
% 0.24/0.46              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.24/0.46          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.24/0.46    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.24/0.46  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.46  thf('2', plain,
% 0.24/0.46      ((m1_subset_1 @ sk_D @ 
% 0.24/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.46  thf(t7_funct_2, axiom,
% 0.24/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.46       ( ( r2_hidden @ C @ A ) =>
% 0.24/0.46         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.46           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.24/0.46  thf('3', plain,
% 0.24/0.46      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.24/0.46         (~ (r2_hidden @ X49 @ X50)
% 0.24/0.46          | ((X51) = (k1_xboole_0))
% 0.24/0.46          | ~ (v1_funct_1 @ X52)
% 0.24/0.46          | ~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.24/0.46          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.24/0.46          | (r2_hidden @ (k1_funct_1 @ X52 @ X49) @ X51))),
% 0.24/0.46      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.24/0.46  thf('4', plain,
% 0.24/0.46      (![X0 : $i]:
% 0.24/0.46         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.24/0.46          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.46          | ~ (v1_funct_1 @ sk_D)
% 0.24/0.46          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.24/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.46  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.46  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.46  thf('7', plain,
% 0.24/0.46      (![X0 : $i]:
% 0.24/0.46         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.24/0.46          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.24/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.24/0.46  thf(t20_zfmisc_1, axiom,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.46         ( k1_tarski @ A ) ) <=>
% 0.24/0.46       ( ( A ) != ( B ) ) ))).
% 0.24/0.46  thf('8', plain,
% 0.24/0.46      (![X46 : $i, X47 : $i]:
% 0.24/0.46         (((X47) != (X46))
% 0.24/0.46          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 0.24/0.46              != (k1_tarski @ X47)))),
% 0.24/0.46      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.24/0.46  thf('9', plain,
% 0.24/0.46      (![X46 : $i]:
% 0.24/0.46         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 0.24/0.46           != (k1_tarski @ X46))),
% 0.24/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.46  thf(d10_xboole_0, axiom,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.46  thf('10', plain,
% 0.24/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.46  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.46  thf(l32_xboole_1, axiom,
% 0.24/0.46    (![A:$i,B:$i]:
% 0.24/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.46  thf('12', plain,
% 0.24/0.46      (![X3 : $i, X5 : $i]:
% 0.24/0.46         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.24/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.46  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.46  thf('14', plain, (![X46 : $i]: ((k1_xboole_0) != (k1_tarski @ X46))),
% 0.24/0.46      inference('demod', [status(thm)], ['9', '13'])).
% 0.24/0.46  thf('15', plain,
% 0.24/0.46      (![X0 : $i]:
% 0.24/0.46         (~ (r2_hidden @ X0 @ sk_A)
% 0.24/0.46          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B)))),
% 0.24/0.46      inference('clc', [status(thm)], ['7', '14'])).
% 0.24/0.46  thf('16', plain,
% 0.24/0.46      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.24/0.46      inference('sup-', [status(thm)], ['1', '15'])).
% 0.24/0.46  thf(t69_enumset1, axiom,
% 0.24/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.46  thf('17', plain,
% 0.24/0.46      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.24/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.46  thf(t70_enumset1, axiom,
% 0.24/0.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.46  thf('18', plain,
% 0.24/0.46      (![X19 : $i, X20 : $i]:
% 0.24/0.46         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.24/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.46  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.24/0.46  thf(zf_stmt_3, axiom,
% 0.24/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.46     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.46       ( ![E:$i]:
% 0.24/0.46         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.24/0.46  thf('19', plain,
% 0.24/0.46      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.46         (~ (r2_hidden @ X16 @ X15)
% 0.24/0.46          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.24/0.46          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.46  thf('20', plain,
% 0.24/0.46      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.24/0.46         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.24/0.46          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.24/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.46  thf('21', plain,
% 0.24/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.46         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.24/0.46          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.24/0.46      inference('sup-', [status(thm)], ['18', '20'])).
% 0.24/0.46  thf('22', plain,
% 0.24/0.46      (![X0 : $i, X1 : $i]:
% 0.24/0.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.24/0.46          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.24/0.46      inference('sup-', [status(thm)], ['17', '21'])).
% 0.24/0.46  thf('23', plain,
% 0.24/0.46      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B)),
% 0.24/0.46      inference('sup-', [status(thm)], ['16', '22'])).
% 0.24/0.46  thf('24', plain,
% 0.24/0.46      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.24/0.46        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.24/0.46        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.24/0.46      inference('sup-', [status(thm)], ['0', '23'])).
% 0.24/0.46  thf('25', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.24/0.46      inference('simplify', [status(thm)], ['24'])).
% 0.24/0.46  thf('26', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.24/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.46  thf('27', plain, ($false),
% 0.24/0.46      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.24/0.46  
% 0.24/0.46  % SZS output end Refutation
% 0.24/0.46  
% 0.24/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
