%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wLiBd5h6Kl

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  294 ( 470 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('8',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X51 @ X48 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C_3 @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C_3 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['15','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wLiBd5h6Kl
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 133 iterations in 0.102s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(l27_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X26 : $i, X27 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ (k1_tarski @ X26) @ X27) | (r2_hidden @ X26 @ X27))),
% 0.21/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.56  thf(t6_mcart_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.56                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.56                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.56                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.56                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.56                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X42 : $i]:
% 0.21/0.56         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X42) @ X42))),
% 0.21/0.56      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.56  thf('2', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.56  thf(t4_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.21/0.56          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.21/0.56          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.56  thf(t61_funct_2, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.56            ( m1_subset_1 @
% 0.21/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_3 @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t7_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X48 @ X49)
% 0.21/0.56          | ((X50) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_funct_1 @ X51)
% 0.21/0.56          | ~ (v1_funct_2 @ X51 @ X49 @ X50)
% 0.21/0.56          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.21/0.56          | (r2_hidden @ (k1_funct_1 @ X51 @ X48) @ X50))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ sk_B_2)
% 0.21/0.56          | ~ (v1_funct_2 @ sk_C_3 @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.21/0.56          | ~ (v1_funct_1 @ sk_C_3)
% 0.21/0.56          | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf('10', plain, ((v1_funct_2 @ sk_C_3 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain, ((v1_funct_1 @ sk_C_3)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ sk_B_2)
% 0.21/0.56          | ((sk_B_2) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.56  thf('13', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ sk_B_2)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ sk_A) @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '14'])).
% 0.21/0.56  thf('16', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_3 @ sk_A) @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('17', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf(t69_enumset1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.56  thf('18', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf(fc3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X24 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.21/0.56  thf('20', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
