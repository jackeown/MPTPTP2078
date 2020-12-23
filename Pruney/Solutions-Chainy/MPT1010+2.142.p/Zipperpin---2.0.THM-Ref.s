%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.drXh2AC53p

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:33 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 116 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  386 (1337 expanded)
%              Number of equality atoms :   38 (  97 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( r2_hidden @ X67 @ X68 )
      | ( X69 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_funct_2 @ X70 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X70 @ X67 ) @ X69 ) ) ),
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

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_B_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','20'])).

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

thf('22',plain,(
    ! [X64: $i] :
      ( ( X64 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X64 ) @ X64 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X64: $i] :
      ( ( X64 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X64 ) @ X64 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.drXh2AC53p
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:15:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 278 iterations in 0.207s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(t65_funct_2, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.46/0.64       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.46/0.64            ( m1_subset_1 @
% 0.46/0.64              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.46/0.64          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.46/0.64  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t7_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( r2_hidden @ C @ A ) =>
% 0.46/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.64           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X67 @ X68)
% 0.46/0.64          | ((X69) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ X70)
% 0.46/0.64          | ~ (v1_funct_2 @ X70 @ X68 @ X69)
% 0.46/0.64          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ X70 @ X67) @ X69))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.46/0.64          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.64          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.46/0.64          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.46/0.64        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '6'])).
% 0.46/0.64  thf(d1_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X6 : $i, X9 : $i]:
% 0.46/0.64         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.46/0.64        | ((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '9'])).
% 0.46/0.64  thf('11', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('12', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('14', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.46/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.64  thf('15', plain, ((r2_hidden @ sk_B_1 @ k1_xboole_0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['12', '14'])).
% 0.46/0.64  thf('16', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf(l33_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X39 : $i, X40 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X39 @ X40)
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X39) @ X40) != (k1_tarski @ X39)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_B_1))
% 0.46/0.64          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '20'])).
% 0.46/0.64  thf(t9_mcart_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.64                 ( ![C:$i,D:$i]:
% 0.46/0.64                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.46/0.64                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X64 : $i]:
% 0.46/0.64         (((X64) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X64) @ X64))),
% 0.46/0.64      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.64  thf(d5_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.64          | (r2_hidden @ X4 @ X1)
% 0.46/0.64          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.64         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X64 : $i]:
% 0.46/0.64         (((X64) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X64) @ X64))),
% 0.46/0.64      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.64          | ~ (r2_hidden @ X4 @ X2)
% 0.46/0.64          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.64          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.46/0.64          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '29'])).
% 0.46/0.64  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.64  thf('32', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '31'])).
% 0.46/0.64  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
