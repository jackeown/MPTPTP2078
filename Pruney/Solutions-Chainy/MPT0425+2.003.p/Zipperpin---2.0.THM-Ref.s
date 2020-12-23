%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cIOYKfhaZF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  182 ( 256 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t57_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
        & ! [D: $i] :
            ( ( r2_hidden @ D @ B )
           => ( r1_xboole_0 @ D @ C ) ) )
     => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ B )
             => ( r1_xboole_0 @ D @ C ) ) )
       => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X5 @ X6 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X5 ) @ ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      | ~ ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X2 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X2 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( r1_xboole_0 @ sk_C_1 @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( r1_xboole_0 @ X9 @ sk_C_1 )
      | ~ ( r2_hidden @ X9 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X7 ) @ X8 )
      | ~ ( r1_xboole_0 @ ( sk_C @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['10'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['5','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cIOYKfhaZF
% 0.13/0.36  % Computer   : n007.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:11:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 19 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.48  thf(t57_setfam_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48         ( ![D:$i]: ( ( r2_hidden @ D @ B ) => ( r1_xboole_0 @ D @ C ) ) ) ) =>
% 0.21/0.48       ( r1_tarski @ C @ ( k3_tarski @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48            ( ![D:$i]: ( ( r2_hidden @ D @ B ) => ( r1_xboole_0 @ D @ C ) ) ) ) =>
% 0.21/0.48          ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t57_setfam_1])).
% 0.21/0.48  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k3_tarski @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((r1_tarski @ sk_C_1 @ (k3_tarski @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t96_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) =
% 0.21/0.48       ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_xboole_0 @ X5 @ X6))
% 0.21/0.48           = (k2_xboole_0 @ (k3_tarski @ X5) @ (k3_tarski @ X6)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t96_zfmisc_1])).
% 0.21/0.48  thf(t73_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.48       ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         ((r1_tarski @ X2 @ X3)
% 0.21/0.48          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 0.21/0.48          | ~ (r1_xboole_0 @ X2 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.48          | ~ (r1_xboole_0 @ X2 @ (k3_tarski @ X0))
% 0.21/0.48          | (r1_tarski @ X2 @ (k3_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((r1_tarski @ sk_C_1 @ (k3_tarski @ sk_A))
% 0.21/0.48        | ~ (r1_xboole_0 @ sk_C_1 @ (k3_tarski @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.48  thf(t98_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k3_tarski @ X7) @ X8)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X9 : $i]: ((r1_xboole_0 @ X9 @ sk_C_1) | ~ (r2_hidden @ X9 @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.21/0.48          | (r1_xboole_0 @ (sk_C @ X0 @ sk_B) @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k3_tarski @ X7) @ X8)
% 0.21/0.48          | ~ (r1_xboole_0 @ (sk_C @ X8 @ X7) @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_1)
% 0.21/0.48        | (r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, ((r1_xboole_0 @ (k3_tarski @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.48  thf('13', plain, ((r1_xboole_0 @ sk_C_1 @ (k3_tarski @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((r1_tarski @ sk_C_1 @ (k3_tarski @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '13'])).
% 0.21/0.48  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
