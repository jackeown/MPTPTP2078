%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uPFlN5Un8V

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  67 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  345 ( 720 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('17',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['9'])).

thf('21',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('25',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uPFlN5Un8V
% 0.12/0.36  % Computer   : n022.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 16:03:41 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 126 iterations in 0.069s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(t3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf(d1_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X4 : $i, X7 : $i]:
% 0.22/0.52         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.52          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ X0 @ X1)
% 0.22/0.52          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.52          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.52  thf(t127_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.22/0.52       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16) @ (k2_zfmisc_1 @ X17 @ X18))
% 0.22/0.52          | ~ (r1_xboole_0 @ X16 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((r2_hidden @ X1 @ X0)
% 0.22/0.52          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf(t131_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( A ) != ( B ) ) =>
% 0.22/0.52       ( ( r1_xboole_0 @
% 0.22/0.52           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.22/0.52           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.22/0.52         ( r1_xboole_0 @
% 0.22/0.52           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.22/0.52           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52        ( ( ( A ) != ( B ) ) =>
% 0.22/0.52          ( ( r1_xboole_0 @
% 0.22/0.52              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.22/0.52              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.22/0.52            ( r1_xboole_0 @
% 0.22/0.52              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.22/0.52              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))
% 0.22/0.52        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.52             (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.52           (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.22/0.52      inference('split', [status(esa)], ['9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16) @ (k2_zfmisc_1 @ X17 @ X18))
% 0.22/0.52          | ~ (r1_xboole_0 @ X15 @ X17))),
% 0.22/0.52      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((r2_hidden @ X1 @ X0)
% 0.22/0.52          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X3) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X0 @ X2)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.22/0.52      inference('split', [status(esa)], ['9'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X4 : $i, X7 : $i]:
% 0.22/0.52         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((((sk_A) = (sk_B)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.52         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))) | 
% 0.22/0.52       ~
% 0.22/0.52       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_2) @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['9'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.52         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.52          (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['10', '21'])).
% 0.22/0.52  thf('23', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X4 : $i, X7 : $i]:
% 0.22/0.52         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.52  thf('25', plain, (((sk_A) = (sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
