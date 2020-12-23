%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rXZuDsts9r

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:39 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 109 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  293 ( 843 expanded)
%              Number of equality atoms :   23 (  68 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('0',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X22 @ X21 ) @ X21 )
      | ( X21
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X22 @ X21 ) @ X21 )
      | ( X21
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('13',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['11','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ ( k2_tarski @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X29: $i] :
      ~ ( m1_subset_1 @ X29 @ sk_A ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rXZuDsts9r
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.51  % Solved by: fo/fo7.sh
% 0.34/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.51  % done 96 iterations in 0.048s
% 0.34/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.51  % SZS output start Refutation
% 0.34/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.51  thf(t10_subset_1, conjecture,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.51            ( ![C:$i]:
% 0.34/0.51              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.34/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.51    (~( ![A:$i,B:$i]:
% 0.34/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.51               ( ![C:$i]:
% 0.34/0.51                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.34/0.51    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.34/0.51  thf('0', plain,
% 0.34/0.51      (![X29 : $i]: (~ (r2_hidden @ X29 @ sk_B) | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf(t41_zfmisc_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.51          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.34/0.51  thf('1', plain,
% 0.34/0.51      (![X21 : $i, X22 : $i]:
% 0.34/0.51         (((X21) = (k1_xboole_0))
% 0.34/0.51          | (r2_hidden @ (sk_C @ X22 @ X21) @ X21)
% 0.34/0.51          | ((X21) = (k1_tarski @ X22)))),
% 0.34/0.51      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.34/0.51  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf(l3_subset_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.34/0.51  thf('3', plain,
% 0.34/0.51      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.34/0.51         (~ (r2_hidden @ X26 @ X27)
% 0.34/0.51          | (r2_hidden @ X26 @ X28)
% 0.34/0.51          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.34/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.34/0.51  thf('4', plain,
% 0.34/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.51  thf('5', plain,
% 0.34/0.51      (![X0 : $i]:
% 0.34/0.51         (((sk_B) = (k1_tarski @ X0))
% 0.34/0.51          | ((sk_B) = (k1_xboole_0))
% 0.34/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.34/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.34/0.51  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('7', plain,
% 0.34/0.51      (![X0 : $i]:
% 0.34/0.51         (((sk_B) = (k1_tarski @ X0)) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.34/0.51      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.34/0.51  thf(d2_subset_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.34/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.34/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.34/0.51  thf('8', plain,
% 0.34/0.51      (![X23 : $i, X24 : $i]:
% 0.34/0.51         (~ (r2_hidden @ X23 @ X24)
% 0.34/0.51          | (m1_subset_1 @ X23 @ X24)
% 0.34/0.51          | (v1_xboole_0 @ X24))),
% 0.34/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.34/0.51  thf(t7_boole, axiom,
% 0.34/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.34/0.51  thf('9', plain,
% 0.34/0.51      (![X3 : $i, X4 : $i]: (~ (r2_hidden @ X3 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.34/0.51      inference('cnf', [status(esa)], [t7_boole])).
% 0.34/0.51  thf('10', plain,
% 0.34/0.51      (![X23 : $i, X24 : $i]:
% 0.34/0.51         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.34/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.34/0.51  thf('11', plain,
% 0.34/0.51      (![X0 : $i]:
% 0.34/0.51         (((sk_B) = (k1_tarski @ X0))
% 0.34/0.51          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.34/0.51      inference('sup-', [status(thm)], ['7', '10'])).
% 0.34/0.51  thf('12', plain,
% 0.34/0.51      (![X21 : $i, X22 : $i]:
% 0.34/0.51         (((X21) = (k1_xboole_0))
% 0.34/0.51          | (r2_hidden @ (sk_C @ X22 @ X21) @ X21)
% 0.34/0.51          | ((X21) = (k1_tarski @ X22)))),
% 0.34/0.51      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.34/0.51  thf('13', plain,
% 0.34/0.51      (![X29 : $i]: (~ (r2_hidden @ X29 @ sk_B) | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('14', plain,
% 0.34/0.51      (![X0 : $i]:
% 0.34/0.51         (((sk_B) = (k1_tarski @ X0))
% 0.34/0.51          | ((sk_B) = (k1_xboole_0))
% 0.34/0.51          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.34/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.51  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('16', plain,
% 0.34/0.51      (![X0 : $i]:
% 0.34/0.51         (((sk_B) = (k1_tarski @ X0))
% 0.34/0.51          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.34/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.34/0.51  thf('17', plain, (![X0 : $i]: ((sk_B) = (k1_tarski @ X0))),
% 0.34/0.51      inference('clc', [status(thm)], ['11', '16'])).
% 0.34/0.51  thf(d10_xboole_0, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.51  thf('18', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.34/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.51  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.34/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.34/0.51  thf(t69_enumset1, axiom,
% 0.34/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.51  thf('20', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.34/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.51  thf(t38_zfmisc_1, axiom,
% 0.34/0.51    (![A:$i,B:$i,C:$i]:
% 0.34/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.34/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.34/0.51  thf('21', plain,
% 0.34/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.34/0.51         ((r2_hidden @ X17 @ X18)
% 0.34/0.51          | ~ (r1_tarski @ (k2_tarski @ X17 @ X19) @ X18))),
% 0.34/0.51      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.34/0.51  thf('22', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.34/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.51  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.34/0.51      inference('sup-', [status(thm)], ['19', '22'])).
% 0.34/0.51  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ sk_B)),
% 0.34/0.51      inference('sup+', [status(thm)], ['17', '23'])).
% 0.34/0.51  thf('25', plain, (![X29 : $i]: ~ (m1_subset_1 @ X29 @ sk_A)),
% 0.34/0.51      inference('demod', [status(thm)], ['0', '24'])).
% 0.34/0.51  thf('26', plain,
% 0.34/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.51  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ sk_B)),
% 0.34/0.51      inference('sup+', [status(thm)], ['17', '23'])).
% 0.34/0.51  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ sk_A)),
% 0.34/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.34/0.51  thf('29', plain,
% 0.34/0.51      (![X23 : $i, X24 : $i]:
% 0.34/0.51         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.34/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.34/0.51  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ sk_A)),
% 0.34/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.51  thf('31', plain, ($false), inference('demod', [status(thm)], ['25', '30'])).
% 0.34/0.51  
% 0.34/0.51  % SZS output end Refutation
% 0.34/0.51  
% 0.34/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
