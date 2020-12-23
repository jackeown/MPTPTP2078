%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4XPGzUgXsh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:35 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   33 (  48 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  247 ( 440 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t151_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ A )
            & ( r2_hidden @ D @ B ) )
         => ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ B ) )
           => ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ sk_A )
      | ~ ( r2_hidden @ X7 @ sk_B )
      | ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X1 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X4 ) @ X5 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X4 ) @ X5 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('17',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_A ) )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('20',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4XPGzUgXsh
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.54  % Solved by: fo/fo7.sh
% 0.34/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.54  % done 307 iterations in 0.094s
% 0.34/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.54  % SZS output start Refutation
% 0.34/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.34/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.34/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.54  thf(t151_zfmisc_1, conjecture,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ![C:$i,D:$i]:
% 0.34/0.54         ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ B ) ) =>
% 0.34/0.54           ( r1_xboole_0 @ C @ D ) ) ) =>
% 0.34/0.54       ( r1_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.34/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.54    (~( ![A:$i,B:$i]:
% 0.34/0.54        ( ( ![C:$i,D:$i]:
% 0.34/0.54            ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ B ) ) =>
% 0.34/0.54              ( r1_xboole_0 @ C @ D ) ) ) =>
% 0.34/0.54          ( r1_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.34/0.54    inference('cnf.neg', [status(esa)], [t151_zfmisc_1])).
% 0.34/0.54  thf('0', plain, (~ (r1_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf(t98_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.34/0.54       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.34/0.54  thf('1', plain,
% 0.34/0.54      (![X4 : $i, X5 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ X4) @ X5)
% 0.34/0.54          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.34/0.54      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.34/0.54  thf('2', plain,
% 0.34/0.54      (![X4 : $i, X5 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ X4) @ X5)
% 0.34/0.54          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.34/0.54      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.34/0.54  thf('3', plain,
% 0.34/0.54      (![X6 : $i, X7 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X6 @ sk_A)
% 0.34/0.54          | ~ (r2_hidden @ X7 @ sk_B)
% 0.34/0.54          | (r1_xboole_0 @ X6 @ X7))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('4', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_A) @ X0)
% 0.34/0.54          | (r1_xboole_0 @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 0.34/0.54          | ~ (r2_hidden @ X1 @ sk_B))),
% 0.34/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.54  thf('5', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.34/0.54          | (r1_xboole_0 @ (sk_C_1 @ X1 @ sk_A) @ (sk_C_1 @ X0 @ sk_B))
% 0.34/0.54          | (r1_xboole_0 @ (k3_tarski @ sk_A) @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['1', '4'])).
% 0.34/0.54  thf('6', plain,
% 0.34/0.54      (![X4 : $i, X5 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ X4) @ X5)
% 0.34/0.54          | ~ (r1_xboole_0 @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.34/0.54      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.34/0.54  thf('7', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_A) @ (sk_C_1 @ X0 @ sk_B))
% 0.34/0.54          | (r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.34/0.54          | (r1_xboole_0 @ (k3_tarski @ sk_A) @ (sk_C_1 @ X0 @ sk_B)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.54  thf('8', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.34/0.54          | (r1_xboole_0 @ (k3_tarski @ sk_A) @ (sk_C_1 @ X0 @ sk_B)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.54  thf(t3_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.34/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.34/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.34/0.54  thf('9', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.54  thf('10', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.54  thf('11', plain,
% 0.34/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.34/0.54          | ~ (r2_hidden @ X2 @ X3)
% 0.34/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.54  thf('12', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X1 @ X0)
% 0.34/0.54          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.34/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.34/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.54  thf('13', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X0 @ X1)
% 0.34/0.54          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.34/0.54          | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['9', '12'])).
% 0.34/0.54  thf('14', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.34/0.54  thf('15', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_B) @ X0)
% 0.34/0.54          | (r1_xboole_0 @ (sk_C_1 @ X0 @ sk_B) @ (k3_tarski @ sk_A)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['8', '14'])).
% 0.34/0.54  thf('16', plain,
% 0.34/0.54      (![X4 : $i, X5 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ (k3_tarski @ X4) @ X5)
% 0.34/0.54          | ~ (r1_xboole_0 @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.34/0.54      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.34/0.54  thf('17', plain,
% 0.34/0.54      (((r1_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_A))
% 0.34/0.54        | (r1_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_A)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('18', plain, ((r1_xboole_0 @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_A))),
% 0.34/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.34/0.54  thf('19', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.34/0.54  thf('20', plain, ((r1_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.34/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.34/0.54  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.34/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
