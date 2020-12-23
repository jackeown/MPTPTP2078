%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.csiQGUiIWv

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:33 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 ( 574 expanded)
%              Number of equality atoms :   31 (  44 expanded)
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

thf('7',plain,(
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

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X64: $i] :
      ( ( X64 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X64 ) @ X64 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ( ( k4_xboole_0 @ X40 @ ( k1_tarski @ X39 ) )
       != X40 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['6','21'])).

thf('23',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.csiQGUiIWv
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:58:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 266 iterations in 0.164s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(t65_funct_2, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.60         ( m1_subset_1 @
% 0.42/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.60       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.60            ( m1_subset_1 @
% 0.42/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.60          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.42/0.60  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t7_funct_2, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60       ( ( r2_hidden @ C @ A ) =>
% 0.42/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.60           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X67 @ X68)
% 0.42/0.60          | ((X69) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_funct_1 @ X70)
% 0.42/0.60          | ~ (v1_funct_2 @ X70 @ X68 @ X69)
% 0.42/0.60          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 0.42/0.60          | (r2_hidden @ (k1_funct_1 @ X70 @ X67) @ X69))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.42/0.60          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.42/0.60          | ~ (v1_funct_1 @ sk_D_1)
% 0.42/0.60          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.42/0.60          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.42/0.60  thf(t9_mcart_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.60                 ( ![C:$i,D:$i]:
% 0.42/0.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.42/0.60                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X64 : $i]:
% 0.42/0.60         (((X64) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X64) @ X64))),
% 0.42/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.42/0.60  thf(d5_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.42/0.60          | (r2_hidden @ X4 @ X1)
% 0.42/0.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.42/0.60         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.42/0.60          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X64 : $i]:
% 0.42/0.60         (((X64) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X64) @ X64))),
% 0.42/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.42/0.60          | ~ (r2_hidden @ X4 @ X2)
% 0.42/0.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.42/0.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.42/0.60          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.42/0.60          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '14'])).
% 0.42/0.60  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.60  thf(t65_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.42/0.60       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X39 : $i, X40 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X39 @ X40)
% 0.42/0.60          | ((k4_xboole_0 @ X40 @ (k1_tarski @ X39)) != (X40)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf(d1_tarski, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.60  thf('20', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.42/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.42/0.60  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['18', '20'])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1)))),
% 0.42/0.60      inference('clc', [status(thm)], ['6', '21'])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X6 : $i, X9 : $i]:
% 0.42/0.60         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.60  thf('26', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['23', '25'])).
% 0.42/0.60  thf('27', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('28', plain, ($false),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
