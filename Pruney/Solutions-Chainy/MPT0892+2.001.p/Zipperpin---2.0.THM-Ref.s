%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BSIveiZ2Tu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  70 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  356 ( 701 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t52_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ~ ( r1_xboole_0 @ A @ D )
        & ~ ( r1_xboole_0 @ B @ E )
        & ~ ( r1_xboole_0 @ C @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ~ ( r1_xboole_0 @ A @ D )
          & ~ ( r1_xboole_0 @ B @ E )
          & ~ ( r1_xboole_0 @ C @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_mcart_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_D )
    | ( r1_xboole_0 @ sk_B @ sk_E )
    | ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_F )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['3'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('6',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X2 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ sk_C ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_E )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('11',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_E ) )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('13',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_E ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ sk_B @ X3 ) @ ( k3_zfmisc_1 @ X0 @ sk_E @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_D )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_D @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('23',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('26',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ X1 @ X3 ) @ ( k3_zfmisc_1 @ sk_D @ X0 @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_F )
    | ( r1_xboole_0 @ sk_A @ sk_D )
    | ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    r1_xboole_0 @ sk_C @ sk_F ),
    inference('sat_resolution*',[status(thm)],['18','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ sk_C ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) ) ),
    inference(simpl_trail,[status(thm)],['8','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BSIveiZ2Tu
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 32 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t52_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.48     ( ( ~( r1_xboole_0 @
% 0.20/0.48            ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) ) =>
% 0.20/0.48       ( ( ~( r1_xboole_0 @ A @ D ) ) & ( ~( r1_xboole_0 @ B @ E ) ) & 
% 0.20/0.48         ( ~( r1_xboole_0 @ C @ F ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.48        ( ( ~( r1_xboole_0 @
% 0.20/0.48               ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) ) ) =>
% 0.20/0.48          ( ( ~( r1_xboole_0 @ A @ D ) ) & ( ~( r1_xboole_0 @ B @ E ) ) & 
% 0.20/0.48            ( ~( r1_xboole_0 @ C @ F ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t52_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (r1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.48          (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r1_xboole_0 @ sk_A @ sk_D)
% 0.20/0.48        | (r1_xboole_0 @ sk_B @ sk_E)
% 0.20/0.48        | (r1_xboole_0 @ sk_C @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r1_xboole_0 @ sk_C @ sk_F)) <= (((r1_xboole_0 @ sk_C @ sk_F)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(t127_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.48       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.48          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_F)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_C @ sk_F)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ sk_C) @ 
% 0.20/0.48           (k2_zfmisc_1 @ X2 @ sk_F)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_C @ sk_F)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ sk_C) @ 
% 0.20/0.48           (k3_zfmisc_1 @ X1 @ X0 @ sk_F)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_C @ sk_F)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((r1_xboole_0 @ sk_B @ sk_E)) <= (((r1_xboole_0 @ sk_B @ sk_E)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.48          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_E)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_B @ sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B) @ X3) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_E) @ X2)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_B @ sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k3_zfmisc_1 @ X1 @ sk_B @ X3) @ 
% 0.20/0.48           (k3_zfmisc_1 @ X0 @ sk_E @ X2)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_B @ sk_E)))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (~ (r1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.48          (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain, (~ ((r1_xboole_0 @ sk_B @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r1_xboole_0 @ sk_A @ sk_D)) <= (((r1_xboole_0 @ sk_A @ sk_D)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_D @ X0)))
% 0.20/0.48         <= (((r1_xboole_0 @ sk_A @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1) @ X3) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ X0) @ X2)))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49          (r1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ X1 @ X3) @ 
% 0.20/0.49           (k3_zfmisc_1 @ sk_D @ X0 @ X2)))
% 0.20/0.49         <= (((r1_xboole_0 @ sk_A @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (~ (r1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.49          (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, (~ ((r1_xboole_0 @ sk_A @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((r1_xboole_0 @ sk_C @ sk_F)) | ((r1_xboole_0 @ sk_A @ sk_D)) | 
% 0.20/0.49       ((r1_xboole_0 @ sk_B @ sk_E))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('30', plain, (((r1_xboole_0 @ sk_C @ sk_F))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['18', '28', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (r1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ sk_C) @ 
% 0.20/0.49          (k3_zfmisc_1 @ X1 @ X0 @ sk_F))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['8', '30'])).
% 0.20/0.49  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
