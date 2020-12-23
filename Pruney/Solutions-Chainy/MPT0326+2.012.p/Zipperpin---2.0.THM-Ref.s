%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W6iWBXoJxe

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :   20
%              Number of atoms          :  353 ( 719 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t139_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
              | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
           => ( r1_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_zfmisc_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X5 ) @ ( k2_zfmisc_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('5',plain,
    ( ( ( r1_tarski @ sk_B @ sk_D )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf('20',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X5 ) @ ( k2_zfmisc_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W6iWBXoJxe
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 29 iterations in 0.019s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(t139_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i,C:$i,D:$i]:
% 0.21/0.48         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.21/0.48             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.21/0.48           ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i,C:$i,D:$i]:
% 0.21/0.48            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.21/0.48                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.21/0.48              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.21/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.21/0.48        | (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.21/0.48           (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_D @ sk_C))))),
% 0.21/0.48      inference('split', [status(esa)], ['1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['1'])).
% 0.21/0.48  thf(t138_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.48       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X5) @ (k2_zfmisc_1 @ X6 @ X7))
% 0.21/0.48          | (r1_tarski @ X5 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((r1_tarski @ sk_B @ sk_D)
% 0.21/0.48         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(t113_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (((X1) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48         | ((sk_A) = (k1_xboole_0))
% 0.21/0.48         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.21/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.48  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))) | 
% 0.21/0.48       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('split', [status(esa)], ['1'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['2', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X5) @ (k2_zfmisc_1 @ X6 @ X7))
% 0.21/0.48          | (r1_tarski @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_D)
% 0.21/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, (((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (((X1) = (k1_xboole_0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.48  thf('29', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('32', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.48  thf('34', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '32', '33'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.35/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
