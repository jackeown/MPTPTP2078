%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g5qP4cabaB

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   44 (  68 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  254 ( 480 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_zfmisc_1 @ X41 )
      | ( X42 = X41 )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g5qP4cabaB
% 0.16/0.38  % Computer   : n021.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 17:19:20 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 97 iterations in 0.060s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.55  thf(t2_tex_2, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.36/0.55           ( r1_tarski @ A @ B ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.36/0.55              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.36/0.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d3_tarski, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X1 : $i, X3 : $i]:
% 0.36/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.55  thf(d4_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X8 @ X7)
% 0.36/0.55          | (r2_hidden @ X8 @ X6)
% 0.36/0.55          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.36/0.55         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.55          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X1 : $i, X3 : $i]:
% 0.36/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.55          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.36/0.55  thf(t1_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.36/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X41 : $i, X42 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X41)
% 0.36/0.55          | ~ (v1_zfmisc_1 @ X41)
% 0.36/0.55          | ((X42) = (X41))
% 0.36/0.55          | ~ (r1_tarski @ X42 @ X41)
% 0.36/0.55          | (v1_xboole_0 @ X42))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.55          | ((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.36/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.36/0.55          | (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(commutativity_k2_tarski, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.55  thf(t12_setfam_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X39 : $i, X40 : $i]:
% 0.36/0.55         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X39 : $i, X40 : $i]:
% 0.36/0.55         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '15'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_A)
% 0.36/0.55        | ~ (v1_zfmisc_1 @ sk_A)
% 0.36/0.55        | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '16'])).
% 0.36/0.55  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf('20', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('25', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.55      inference('sup+', [status(thm)], ['21', '24'])).
% 0.36/0.55  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
