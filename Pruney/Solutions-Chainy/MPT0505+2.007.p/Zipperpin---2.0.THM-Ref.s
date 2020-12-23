%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uetzw3OFZl

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  265 ( 352 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) @ X34 )
        = ( k7_relat_1 @ X32 @ ( k3_xboole_0 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t103_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_relat_1])).

thf('1',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ( ( k7_relat_1 @ X39 @ X40 )
        = X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X35: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X35: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13','18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k7_relat_1 @ sk_C @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uetzw3OFZl
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:14:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 23 iterations in 0.020s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(t100_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.51         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.51         (((k7_relat_1 @ (k7_relat_1 @ X32 @ X33) @ X34)
% 0.22/0.51            = (k7_relat_1 @ X32 @ (k3_xboole_0 @ X33 @ X34)))
% 0.22/0.51          | ~ (v1_relat_1 @ X32))),
% 0.22/0.51      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.51  thf(t103_relat_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r1_tarski @ A @ B ) =>
% 0.22/0.51         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( v1_relat_1 @ C ) =>
% 0.22/0.51          ( ( r1_tarski @ A @ B ) =>
% 0.22/0.51            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.22/0.51              ( k7_relat_1 @ C @ A ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t103_relat_1])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.51         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      ((((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.22/0.51          != (k7_relat_1 @ sk_C @ sk_A))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t71_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.51  thf('4', plain, (![X35 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.22/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.51  thf(t97_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.51         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X39 : $i, X40 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 0.22/0.51          | ((k7_relat_1 @ X39 @ X40) = (X39))
% 0.22/0.51          | ~ (v1_relat_1 @ X39))),
% 0.22/0.51      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.51          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.51  thf('7', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.51          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '8'])).
% 0.22/0.51  thf(t90_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.51         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X37 : $i, X38 : $i]:
% 0.22/0.51         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.22/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.22/0.51          | ~ (v1_relat_1 @ X37))),
% 0.22/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.22/0.51          = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ sk_B))
% 0.22/0.51        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, (![X35 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.22/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.51  thf('13', plain, (![X35 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.22/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.51  thf(commutativity_k2_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.51  thf(t12_setfam_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X29 : $i, X30 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X29 : $i, X30 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.51  thf('20', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13', '18', '19'])).
% 0.22/0.51  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '20', '21'])).
% 0.22/0.51  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
