%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7tpPCfDdPh

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:43 EST 2020

% Result     : Timeout 57.79s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  361 ( 699 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ( r1_tarski @ ( sk_E @ X12 @ X13 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('2',plain,
    ( ( r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ ( k2_xboole_0 @ X7 @ X9 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X7 ) @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ ( sk_D @ X12 @ X13 @ X11 ) @ ( sk_E @ X12 @ X13 @ X11 ) ) )
      | ~ ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X14: $i] :
      ( ~ ( v1_finset_1 @ X14 )
      | ~ ( r1_tarski @ X14 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X14 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ( r1_tarski @ ( sk_D @ X12 @ X13 @ X11 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('23',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ( v1_finset_1 @ ( sk_D @ X12 @ X13 @ X11 ) )
      | ~ ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('28',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['20','25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7tpPCfDdPh
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:37:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 57.79/57.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 57.79/57.99  % Solved by: fo/fo7.sh
% 57.79/57.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.79/57.99  % done 5004 iterations in 57.520s
% 57.79/57.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 57.79/57.99  % SZS output start Refutation
% 57.79/57.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 57.79/57.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 57.79/57.99  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 57.79/57.99  thf(sk_B_type, type, sk_B: $i).
% 57.79/57.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 57.79/57.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 57.79/57.99  thf(sk_A_type, type, sk_A: $i).
% 57.79/57.99  thf(sk_C_type, type, sk_C: $i).
% 57.79/57.99  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 57.79/57.99  thf(t33_finset_1, conjecture,
% 57.79/57.99    (![A:$i,B:$i,C:$i]:
% 57.79/57.99     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 57.79/57.99          ( ![D:$i]:
% 57.79/57.99            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 57.79/57.99                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 57.79/57.99  thf(zf_stmt_0, negated_conjecture,
% 57.79/57.99    (~( ![A:$i,B:$i,C:$i]:
% 57.79/57.99        ( ~( ( v1_finset_1 @ A ) & 
% 57.79/57.99             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 57.79/57.99             ( ![D:$i]:
% 57.79/57.99               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 57.79/57.99                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 57.79/57.99    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 57.79/57.99  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf(t32_finset_1, axiom,
% 57.79/57.99    (![A:$i,B:$i,C:$i]:
% 57.79/57.99     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 57.79/57.99          ( ![D:$i,E:$i]:
% 57.79/57.99            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 57.79/57.99                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 57.79/57.99                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 57.79/57.99  thf('1', plain,
% 57.79/57.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 57.79/57.99         (~ (v1_finset_1 @ X11)
% 57.79/57.99          | (r1_tarski @ (sk_E @ X12 @ X13 @ X11) @ X12)
% 57.79/57.99          | ~ (r1_tarski @ X11 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 57.79/57.99      inference('cnf', [status(esa)], [t32_finset_1])).
% 57.79/57.99  thf('2', plain,
% 57.79/57.99      (((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)
% 57.79/57.99        | ~ (v1_finset_1 @ sk_A))),
% 57.79/57.99      inference('sup-', [status(thm)], ['0', '1'])).
% 57.79/57.99  thf('3', plain, ((v1_finset_1 @ sk_A)),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('4', plain, ((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 57.79/57.99      inference('demod', [status(thm)], ['2', '3'])).
% 57.79/57.99  thf(t12_xboole_1, axiom,
% 57.79/57.99    (![A:$i,B:$i]:
% 57.79/57.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 57.79/57.99  thf('5', plain,
% 57.79/57.99      (![X5 : $i, X6 : $i]:
% 57.79/57.99         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 57.79/57.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 57.79/57.99  thf('6', plain,
% 57.79/57.99      (((k2_xboole_0 @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C) = (sk_C))),
% 57.79/57.99      inference('sup-', [status(thm)], ['4', '5'])).
% 57.79/57.99  thf(commutativity_k2_xboole_0, axiom,
% 57.79/57.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 57.79/57.99  thf('7', plain,
% 57.79/57.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 57.79/57.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 57.79/57.99  thf('8', plain,
% 57.79/57.99      (((k2_xboole_0 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A)) = (sk_C))),
% 57.79/57.99      inference('demod', [status(thm)], ['6', '7'])).
% 57.79/57.99  thf(t120_zfmisc_1, axiom,
% 57.79/57.99    (![A:$i,B:$i,C:$i]:
% 57.79/57.99     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 57.79/57.99         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 57.79/57.99       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 57.79/57.99         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 57.79/57.99  thf('9', plain,
% 57.79/57.99      (![X7 : $i, X9 : $i, X10 : $i]:
% 57.79/57.99         ((k2_zfmisc_1 @ X10 @ (k2_xboole_0 @ X7 @ X9))
% 57.79/57.99           = (k2_xboole_0 @ (k2_zfmisc_1 @ X10 @ X7) @ (k2_zfmisc_1 @ X10 @ X9)))),
% 57.79/57.99      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 57.79/57.99  thf('10', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('11', plain,
% 57.79/57.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 57.79/57.99         (~ (v1_finset_1 @ X11)
% 57.79/57.99          | (r1_tarski @ X11 @ 
% 57.79/57.99             (k2_zfmisc_1 @ (sk_D @ X12 @ X13 @ X11) @ (sk_E @ X12 @ X13 @ X11)))
% 57.79/57.99          | ~ (r1_tarski @ X11 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 57.79/57.99      inference('cnf', [status(esa)], [t32_finset_1])).
% 57.79/57.99  thf('12', plain,
% 57.79/57.99      (((r1_tarski @ sk_A @ 
% 57.79/57.99         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 57.79/57.99          (sk_E @ sk_C @ sk_B @ sk_A)))
% 57.79/57.99        | ~ (v1_finset_1 @ sk_A))),
% 57.79/57.99      inference('sup-', [status(thm)], ['10', '11'])).
% 57.79/57.99  thf('13', plain, ((v1_finset_1 @ sk_A)),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('14', plain,
% 57.79/57.99      ((r1_tarski @ sk_A @ 
% 57.79/57.99        (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 57.79/57.99         (sk_E @ sk_C @ sk_B @ sk_A)))),
% 57.79/57.99      inference('demod', [status(thm)], ['12', '13'])).
% 57.79/57.99  thf(t10_xboole_1, axiom,
% 57.79/57.99    (![A:$i,B:$i,C:$i]:
% 57.79/57.99     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 57.79/57.99  thf('15', plain,
% 57.79/57.99      (![X2 : $i, X3 : $i, X4 : $i]:
% 57.79/57.99         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 57.79/57.99      inference('cnf', [status(esa)], [t10_xboole_1])).
% 57.79/57.99  thf('16', plain,
% 57.79/57.99      (![X0 : $i]:
% 57.79/57.99         (r1_tarski @ sk_A @ 
% 57.79/57.99          (k2_xboole_0 @ X0 @ 
% 57.79/57.99           (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 57.79/57.99            (sk_E @ sk_C @ sk_B @ sk_A))))),
% 57.79/57.99      inference('sup-', [status(thm)], ['14', '15'])).
% 57.79/57.99  thf('17', plain,
% 57.79/57.99      (![X0 : $i]:
% 57.79/57.99         (r1_tarski @ sk_A @ 
% 57.79/57.99          (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 57.79/57.99           (k2_xboole_0 @ X0 @ (sk_E @ sk_C @ sk_B @ sk_A))))),
% 57.79/57.99      inference('sup+', [status(thm)], ['9', '16'])).
% 57.79/57.99  thf('18', plain,
% 57.79/57.99      ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 57.79/57.99      inference('sup+', [status(thm)], ['8', '17'])).
% 57.79/57.99  thf('19', plain,
% 57.79/57.99      (![X14 : $i]:
% 57.79/57.99         (~ (v1_finset_1 @ X14)
% 57.79/57.99          | ~ (r1_tarski @ X14 @ sk_B)
% 57.79/57.99          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X14 @ sk_C)))),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('20', plain,
% 57.79/57.99      ((~ (r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 57.79/57.99        | ~ (v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 57.79/57.99      inference('sup-', [status(thm)], ['18', '19'])).
% 57.79/57.99  thf('21', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('22', plain,
% 57.79/57.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 57.79/57.99         (~ (v1_finset_1 @ X11)
% 57.79/57.99          | (r1_tarski @ (sk_D @ X12 @ X13 @ X11) @ X13)
% 57.79/57.99          | ~ (r1_tarski @ X11 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 57.79/57.99      inference('cnf', [status(esa)], [t32_finset_1])).
% 57.79/57.99  thf('23', plain,
% 57.79/57.99      (((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 57.79/57.99        | ~ (v1_finset_1 @ sk_A))),
% 57.79/57.99      inference('sup-', [status(thm)], ['21', '22'])).
% 57.79/57.99  thf('24', plain, ((v1_finset_1 @ sk_A)),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('25', plain, ((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 57.79/57.99      inference('demod', [status(thm)], ['23', '24'])).
% 57.79/57.99  thf('26', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('27', plain,
% 57.79/57.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 57.79/57.99         (~ (v1_finset_1 @ X11)
% 57.79/57.99          | (v1_finset_1 @ (sk_D @ X12 @ X13 @ X11))
% 57.79/57.99          | ~ (r1_tarski @ X11 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 57.79/57.99      inference('cnf', [status(esa)], [t32_finset_1])).
% 57.79/57.99  thf('28', plain,
% 57.79/57.99      (((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 57.79/57.99      inference('sup-', [status(thm)], ['26', '27'])).
% 57.79/57.99  thf('29', plain, ((v1_finset_1 @ sk_A)),
% 57.79/57.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.79/57.99  thf('30', plain, ((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 57.79/57.99      inference('demod', [status(thm)], ['28', '29'])).
% 57.79/57.99  thf('31', plain, ($false),
% 57.79/57.99      inference('demod', [status(thm)], ['20', '25', '30'])).
% 57.79/57.99  
% 57.79/57.99  % SZS output end Refutation
% 57.79/57.99  
% 57.79/58.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
