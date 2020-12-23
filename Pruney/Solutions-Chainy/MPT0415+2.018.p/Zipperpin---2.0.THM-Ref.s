%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V0lTyl34Ww

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:11 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  250 ( 336 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_setfam_1 @ X11 @ ( k7_setfam_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('3',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X4 )
      | ( r2_hidden @ ( k3_subset_1 @ X5 @ ( sk_D_1 @ X4 @ X6 @ X5 ) ) @ X6 )
      | ( X4
        = ( k7_setfam_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V0lTyl34Ww
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 608 iterations in 0.462s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.90  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.69/0.90  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.69/0.90  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.90  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.90  thf(t46_setfam_1, conjecture,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.90            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i,B:$i]:
% 0.69/0.90        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.90               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.69/0.90  thf('1', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(involutiveness_k7_setfam_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.69/0.90  thf('2', plain,
% 0.69/0.90      (![X10 : $i, X11 : $i]:
% 0.69/0.90         (((k7_setfam_1 @ X11 @ (k7_setfam_1 @ X11 @ X10)) = (X10))
% 0.69/0.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.69/0.90      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.69/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.90  thf('4', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('5', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.69/0.90      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.90  thf(t4_subset_1, axiom,
% 0.69/0.90    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.69/0.90  thf('6', plain,
% 0.69/0.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.90  thf('7', plain,
% 0.69/0.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.90  thf(d8_setfam_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90       ( ![C:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.69/0.90             ( ![D:$i]:
% 0.69/0.90               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.90                 ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.90                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.69/0.90          | (r2_hidden @ (sk_D_1 @ X4 @ X6 @ X5) @ X4)
% 0.69/0.90          | (r2_hidden @ (k3_subset_1 @ X5 @ (sk_D_1 @ X4 @ X6 @ X5)) @ X6)
% 0.69/0.90          | ((X4) = (k7_setfam_1 @ X5 @ X6))
% 0.69/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.69/0.90      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.69/0.90  thf('9', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.69/0.90          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ X1))
% 0.69/0.90          | (r2_hidden @ 
% 0.69/0.90             (k3_subset_1 @ X0 @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0)) @ X1)
% 0.69/0.90          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['7', '8'])).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.69/0.90          | (r2_hidden @ 
% 0.69/0.90             (k3_subset_1 @ X0 @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.69/0.90             k1_xboole_0)
% 0.69/0.90          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['6', '9'])).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.90  thf(t5_subset, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.69/0.90          ( v1_xboole_0 @ C ) ) ))).
% 0.69/0.90  thf('12', plain,
% 0.69/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.90         (~ (r2_hidden @ X18 @ X19)
% 0.69/0.90          | ~ (v1_xboole_0 @ X20)
% 0.69/0.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t5_subset])).
% 0.69/0.90  thf('13', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.90  thf('14', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.69/0.90          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.69/0.90             k1_xboole_0)
% 0.69/0.90          | ~ (v1_xboole_0 @ X1))),
% 0.69/0.90      inference('sup-', [status(thm)], ['10', '13'])).
% 0.69/0.90  thf('15', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.90  thf('16', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X1)
% 0.69/0.90          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.90      inference('clc', [status(thm)], ['14', '15'])).
% 0.69/0.90  thf('17', plain,
% 0.69/0.90      (![X0 : $i]: (((k1_xboole_0) = (sk_B)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup+', [status(thm)], ['5', '16'])).
% 0.69/0.90  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('19', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.69/0.90  thf('20', plain, ($false), inference('sup-', [status(thm)], ['0', '19'])).
% 0.69/0.90  
% 0.69/0.90  % SZS output end Refutation
% 0.69/0.90  
% 0.74/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
