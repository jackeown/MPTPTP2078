%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pNdRjgThmp

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 ( 459 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t104_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) )
        & ! [F: $i,G: $i] :
            ~ ( ( A
                = ( k4_tarski @ F @ G ) )
              & ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) )
              & ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_hidden @ ( sk_F @ X13 @ X12 @ X11 @ X10 @ X9 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t104_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X1 @ X2 @ X3 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) @ ( k3_xboole_0 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('13',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_hidden @ ( sk_G @ X13 @ X12 @ X11 @ X10 @ X9 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t104_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_G @ X0 @ X1 @ X2 @ X3 @ ( sk_C @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pNdRjgThmp
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 21:01:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 69 iterations in 0.057s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(t127_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.52       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.52          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.52          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_C_1 @ sk_D)) <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X3 @ X4)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf(t104_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.52     ( ~( ( r2_hidden @
% 0.21/0.52            A @ 
% 0.21/0.52            ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 0.21/0.52          ( ![F:$i,G:$i]:
% 0.21/0.52            ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 0.21/0.52                 ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 0.21/0.52                 ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X9 @ 
% 0.21/0.52             (k3_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.21/0.52              (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.52          | (r2_hidden @ (sk_F @ X13 @ X12 @ X11 @ X10 @ X9) @ 
% 0.21/0.52             (k3_xboole_0 @ X10 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t104_zfmisc_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (sk_F @ X0 @ X1 @ X2 @ X3 @ 
% 0.21/0.52              (sk_C @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X3 @ X2))) @ 
% 0.21/0.52             (k3_xboole_0 @ X3 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.21/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2) @ (k2_zfmisc_1 @ X0 @ X3))
% 0.21/0.52          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((![X0 : $i, X1 : $i]:
% 0.21/0.52          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.52         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.52          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((r1_xboole_0 @ sk_C_1 @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('13', plain, (((r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['2', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X3 @ X4)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X9 @ 
% 0.21/0.52             (k3_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.21/0.52              (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.52          | (r2_hidden @ (sk_G @ X13 @ X12 @ X11 @ X10 @ X9) @ 
% 0.21/0.52             (k3_xboole_0 @ X11 @ X13)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t104_zfmisc_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (sk_G @ X0 @ X1 @ X2 @ X3 @ 
% 0.21/0.52              (sk_C @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X3 @ X2))) @ 
% 0.21/0.52             (k3_xboole_0 @ X2 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.21/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X3 @ X0))
% 0.21/0.52          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.52  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
