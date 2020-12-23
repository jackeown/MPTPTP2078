%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8GHBDsv99v

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  268 ( 388 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) @ X4 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v1_zfmisc_1 @ X17 )
      | ( X18 = X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X10 ) ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8GHBDsv99v
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 58 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t2_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.20/0.48           ( r1_tarski @ A @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.20/0.48              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.20/0.48  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t17_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.20/0.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.48  thf(t12_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5)) @ X4)),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t1_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X17)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X17)
% 0.20/0.48          | ((X18) = (X17))
% 0.20/0.48          | ~ (r1_tarski @ X18 @ X17)
% 0.20/0.48          | (v1_xboole_0 @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.20/0.48          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (~ (v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_A)
% 0.20/0.48        | ~ (v1_zfmisc_1 @ sk_A)
% 0.20/0.48        | ((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.48  thf('10', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_A)
% 0.20/0.48        | ((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X6 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf(t31_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( r1_tarski @
% 0.20/0.48       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.20/0.48       ( k2_xboole_0 @ B @ C ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (r1_tarski @ 
% 0.20/0.48          (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)) @ 
% 0.20/0.48          (k2_xboole_0 @ X9 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (r1_tarski @ 
% 0.20/0.48          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ 
% 0.20/0.48           (k1_setfam_1 @ (k2_tarski @ X8 @ X10))) @ 
% 0.20/0.48          (k2_xboole_0 @ X9 @ X10))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (r1_tarski @ 
% 0.20/0.48          (k2_xboole_0 @ k1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.20/0.48          (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['16', '20'])).
% 0.20/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.48  thf('22', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf(t12_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.48  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '24', '25'])).
% 0.20/0.48  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '26'])).
% 0.20/0.48  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
