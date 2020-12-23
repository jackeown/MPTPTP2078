%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q40IcHImus

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:00 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 156 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
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

thf('1',plain,(
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

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r1_setfam_1 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t136_zfmisc_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ C @ B )
            & ~ ( r2_tarski @ C @ B )
            & ~ ( r2_hidden @ C @ B ) )
      & ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r1_tarski @ D @ C ) )
         => ( r2_hidden @ D @ B ) )
      & ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( sk_B_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','8'])).

thf('10',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q40IcHImus
% 0.15/0.38  % Computer   : n021.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:00:49 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 38 iterations in 0.022s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.25/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.51  thf(r2_tarski_type, type, r2_tarski: $i > $i > $o).
% 0.25/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.25/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.51  thf(t7_xboole_0, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.25/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.25/0.51  thf('0', plain,
% 0.25/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.25/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.25/0.51  thf(t21_setfam_1, conjecture,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]:
% 0.25/0.51        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.25/0.51  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(d2_setfam_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.25/0.51       ( ![C:$i]:
% 0.25/0.51         ( ~( ( r2_hidden @ C @ A ) & 
% 0.25/0.51              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.51         ((r2_hidden @ (sk_D @ X14 @ X15) @ X15)
% 0.25/0.51          | ~ (r2_hidden @ X14 @ X16)
% 0.25/0.51          | ~ (r1_setfam_1 @ X16 @ X15))),
% 0.25/0.51      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.25/0.51          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.25/0.51  thf('4', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.25/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.25/0.51  thf(t136_zfmisc_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ?[B:$i]:
% 0.25/0.51       ( ( ![C:$i]:
% 0.25/0.51           ( ~( ( r1_tarski @ C @ B ) & ( ~( r2_tarski @ C @ B ) ) & 
% 0.25/0.51                ( ~( r2_hidden @ C @ B ) ) ) ) ) & 
% 0.25/0.51         ( ![C:$i]:
% 0.25/0.51           ( ( r2_hidden @ C @ B ) => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) ) ) & 
% 0.25/0.51         ( ![C:$i,D:$i]:
% 0.25/0.51           ( ( ( r2_hidden @ C @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.25/0.51             ( r2_hidden @ D @ B ) ) ) & 
% 0.25/0.51         ( r2_hidden @ A @ B ) ) ))).
% 0.25/0.51  thf('5', plain, (![X6 : $i]: (r2_hidden @ X6 @ (sk_B_1 @ X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 0.25/0.51  thf(t3_xboole_0, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.25/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.25/0.51  thf('6', plain,
% 0.25/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X2 @ X0)
% 0.25/0.51          | ~ (r2_hidden @ X2 @ X3)
% 0.25/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('7', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (r1_xboole_0 @ (sk_B_1 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.25/0.51  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.25/0.51      inference('sup-', [status(thm)], ['4', '7'])).
% 0.25/0.51  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.25/0.51      inference('clc', [status(thm)], ['3', '8'])).
% 0.25/0.51  thf('10', plain, (((sk_A) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['0', '9'])).
% 0.25/0.51  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('12', plain, ($false),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
