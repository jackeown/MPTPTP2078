%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TdZDvX7AQm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:59 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 127 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('2',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_setfam_1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TdZDvX7AQm
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:08:36 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 18 iterations in 0.015s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.24/0.51  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.51  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.51  thf(t7_xboole_0, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.51  thf(t21_setfam_1, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.24/0.51  thf('2', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(d2_setfam_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.24/0.51       ( ![C:$i]:
% 0.24/0.51         ( ~( ( r2_hidden @ C @ A ) & 
% 0.24/0.51              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.51         ((r2_hidden @ (sk_D @ X2 @ X3) @ X3)
% 0.24/0.51          | ~ (r2_hidden @ X2 @ X4)
% 0.24/0.51          | ~ (r1_setfam_1 @ X4 @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.24/0.51          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      ((((sk_A) = (k1_xboole_0))
% 0.24/0.51        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.24/0.51  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      ((r2_hidden @ (sk_D @ (sk_B @ sk_A) @ k1_xboole_0) @ k1_xboole_0)),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.24/0.51  thf(t4_subset_1, axiom,
% 0.24/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.51  thf(t5_subset, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.24/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X10 @ X11)
% 0.24/0.51          | ~ (v1_xboole_0 @ X12)
% 0.24/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.51  thf('11', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.24/0.51      inference('sup-', [status(thm)], ['7', '10'])).
% 0.24/0.51  thf('12', plain, ($false), inference('sup-', [status(thm)], ['0', '11'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
