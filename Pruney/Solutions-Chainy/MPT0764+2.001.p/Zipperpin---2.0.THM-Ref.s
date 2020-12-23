%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBdPnXL4fW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:21 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   45 (  85 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  335 (1056 expanded)
%              Number of equality atoms :   15 (  49 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t10_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v2_wellord1 @ A )
         => ! [B: $i] :
              ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
                & ( B != k1_xboole_0 )
                & ! [C: $i] :
                    ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( r2_hidden @ D @ B )
                         => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) )
      <=> ( v2_wellord1 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf(t9_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_wellord1 @ B @ A )
       => ! [C: $i] :
            ~ ( ( r1_tarski @ C @ A )
              & ( C != k1_xboole_0 )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ C )
                    & ! [E: $i] :
                        ( ( r2_hidden @ E @ C )
                       => ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_wellord1 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X4 @ X1 ) @ X4 )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t9_wellord1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i] :
      ( ~ ( r2_hidden @ X5 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ X5 ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_wellord1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X4 @ X1 ) @ X3 ) @ X1 )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t9_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v2_wellord1 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_B @ sk_A ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( ~ ( r2_hidden @ X5 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_D_1 @ X5 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBdPnXL4fW
% 0.16/0.38  % Computer   : n020.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:09:37 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 20 iterations in 0.015s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.25/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.51  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.25/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.25/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.25/0.51  thf(t10_wellord1, conjecture,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ A ) =>
% 0.25/0.51       ( ( v2_wellord1 @ A ) =>
% 0.25/0.51         ( ![B:$i]:
% 0.25/0.51           ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 0.25/0.51                ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.25/0.51                ( ![C:$i]:
% 0.25/0.51                  ( ~( ( r2_hidden @ C @ B ) & 
% 0.25/0.51                       ( ![D:$i]:
% 0.25/0.51                         ( ( r2_hidden @ D @ B ) =>
% 0.25/0.51                           ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]:
% 0.25/0.51        ( ( v1_relat_1 @ A ) =>
% 0.25/0.51          ( ( v2_wellord1 @ A ) =>
% 0.25/0.51            ( ![B:$i]:
% 0.25/0.51              ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 0.25/0.51                   ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.25/0.51                   ( ![C:$i]:
% 0.25/0.51                     ( ~( ( r2_hidden @ C @ B ) & 
% 0.25/0.51                          ( ![D:$i]:
% 0.25/0.51                            ( ( r2_hidden @ D @ B ) =>
% 0.25/0.51                              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t10_wellord1])).
% 0.25/0.51  thf('0', plain, ((r1_tarski @ sk_B @ (k3_relat_1 @ sk_A))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(t8_wellord1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ A ) =>
% 0.25/0.51       ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) ) <=> ( v2_wellord1 @ A ) ) ))).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v2_wellord1 @ X0)
% 0.25/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.25/0.51          | ~ (v1_relat_1 @ X0))),
% 0.25/0.51      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.25/0.51  thf(t9_wellord1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ B ) =>
% 0.25/0.51       ( ( r2_wellord1 @ B @ A ) =>
% 0.25/0.51         ( ![C:$i]:
% 0.25/0.51           ( ~( ( r1_tarski @ C @ A ) & ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.25/0.51                ( ![D:$i]:
% 0.25/0.51                  ( ~( ( r2_hidden @ D @ C ) & 
% 0.25/0.51                       ( ![E:$i]:
% 0.25/0.51                         ( ( r2_hidden @ E @ C ) =>
% 0.25/0.51                           ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.25/0.51         (~ (r2_wellord1 @ X1 @ X2)
% 0.25/0.51          | (r2_hidden @ (sk_D @ X4 @ X1) @ X4)
% 0.25/0.51          | ((X4) = (k1_xboole_0))
% 0.25/0.51          | ~ (r1_tarski @ X4 @ X2)
% 0.25/0.51          | ~ (v1_relat_1 @ X1))),
% 0.25/0.51      inference('cnf', [status(esa)], [t9_wellord1])).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (v1_relat_1 @ X0)
% 0.25/0.51          | ~ (v2_wellord1 @ X0)
% 0.25/0.51          | ~ (v1_relat_1 @ X0)
% 0.25/0.51          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.25/0.51          | ((X1) = (k1_xboole_0))
% 0.25/0.51          | (r2_hidden @ (sk_D @ X1 @ X0) @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((r2_hidden @ (sk_D @ X1 @ X0) @ X1)
% 0.25/0.51          | ((X1) = (k1_xboole_0))
% 0.25/0.51          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.25/0.51          | ~ (v2_wellord1 @ X0)
% 0.25/0.51          | ~ (v1_relat_1 @ X0))),
% 0.25/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      ((~ (v1_relat_1 @ sk_A)
% 0.25/0.51        | ~ (v2_wellord1 @ sk_A)
% 0.25/0.51        | ((sk_B) = (k1_xboole_0))
% 0.25/0.51        | (r2_hidden @ (sk_D @ sk_B @ sk_A) @ sk_B))),
% 0.25/0.51      inference('sup-', [status(thm)], ['0', '4'])).
% 0.25/0.51  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('7', plain, ((v2_wellord1 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      ((((sk_B) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ sk_B @ sk_A) @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.25/0.51  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('10', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A) @ sk_B)),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      (![X5 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X5 @ sk_B) | (r2_hidden @ (sk_D_1 @ X5) @ sk_B))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('12', plain, ((r2_hidden @ (sk_D_1 @ (sk_D @ sk_B @ sk_A)) @ sk_B)),
% 0.25/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.51  thf('13', plain, ((r1_tarski @ sk_B @ (k3_relat_1 @ sk_A))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('14', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v2_wellord1 @ X0)
% 0.25/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.25/0.51          | ~ (v1_relat_1 @ X0))),
% 0.25/0.51      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.25/0.51  thf('15', plain,
% 0.25/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.51         (~ (r2_wellord1 @ X1 @ X2)
% 0.25/0.51          | ~ (r2_hidden @ X3 @ X4)
% 0.25/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ X4 @ X1) @ X3) @ X1)
% 0.25/0.51          | ((X4) = (k1_xboole_0))
% 0.25/0.51          | ~ (r1_tarski @ X4 @ X2)
% 0.25/0.51          | ~ (v1_relat_1 @ X1))),
% 0.25/0.51      inference('cnf', [status(esa)], [t9_wellord1])).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         (~ (v1_relat_1 @ X0)
% 0.25/0.51          | ~ (v2_wellord1 @ X0)
% 0.25/0.51          | ~ (v1_relat_1 @ X0)
% 0.25/0.51          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.25/0.51          | ((X1) = (k1_xboole_0))
% 0.25/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 0.25/0.51          | ~ (r2_hidden @ X2 @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.51  thf('17', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X2 @ X1)
% 0.25/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 0.25/0.51          | ((X1) = (k1_xboole_0))
% 0.25/0.51          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.25/0.51          | ~ (v2_wellord1 @ X0)
% 0.25/0.51          | ~ (v1_relat_1 @ X0))),
% 0.25/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.25/0.51  thf('18', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v1_relat_1 @ sk_A)
% 0.25/0.51          | ~ (v2_wellord1 @ sk_A)
% 0.25/0.51          | ((sk_B) = (k1_xboole_0))
% 0.25/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.25/0.51          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.25/0.51      inference('sup-', [status(thm)], ['13', '17'])).
% 0.25/0.51  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('20', plain, ((v2_wellord1 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('21', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (((sk_B) = (k1_xboole_0))
% 0.25/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.25/0.51          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.25/0.51  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('23', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((r2_hidden @ (k4_tarski @ (sk_D @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.25/0.51          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.25/0.51  thf('24', plain,
% 0.25/0.51      ((r2_hidden @ 
% 0.25/0.51        (k4_tarski @ (sk_D @ sk_B @ sk_A) @ (sk_D_1 @ (sk_D @ sk_B @ sk_A))) @ 
% 0.25/0.51        sk_A)),
% 0.25/0.51      inference('sup-', [status(thm)], ['12', '23'])).
% 0.25/0.51  thf('25', plain,
% 0.25/0.51      (![X5 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X5 @ sk_B)
% 0.25/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ (sk_D_1 @ X5)) @ sk_A))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('26', plain, (~ (r2_hidden @ (sk_D @ sk_B @ sk_A) @ sk_B)),
% 0.25/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.25/0.51  thf('27', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A) @ sk_B)),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.25/0.51  thf('28', plain, ($false), inference('demod', [status(thm)], ['26', '27'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
