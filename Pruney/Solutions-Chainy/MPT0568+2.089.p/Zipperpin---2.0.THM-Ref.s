%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I0gpTze6nq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:59 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   57 (  57 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  317 ( 317 expanded)
%              Number of equality atoms :   36 (  36 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k10_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ X27 @ ( sk_D @ X28 @ X26 @ X27 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X0 @ X1 ) ) @ ( sk_D @ X0 @ X1 @ ( sk_B @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 != X18 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X18 ) )
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X18 ) )
     != ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X21: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X18: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['13','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','22'])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I0gpTze6nq
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:44:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 392 iterations in 0.164s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(t172_relat_1, conjecture,
% 0.39/0.62    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.39/0.62  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t7_xboole_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.62  thf(t166_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ C ) =>
% 0.39/0.62       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.39/0.62         ( ?[D:$i]:
% 0.39/0.62           ( ( r2_hidden @ D @ B ) & 
% 0.39/0.62             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.39/0.62             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X27 @ (k10_relat_1 @ X28 @ X26))
% 0.39/0.62          | (r2_hidden @ (k4_tarski @ X27 @ (sk_D @ X28 @ X26 @ X27)) @ X28)
% 0.39/0.62          | ~ (v1_relat_1 @ X28))),
% 0.39/0.62      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X1)
% 0.39/0.62          | (r2_hidden @ 
% 0.39/0.62             (k4_tarski @ (sk_B @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.39/0.62              (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.39/0.62             X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf(l1_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X15 : $i, X17 : $i]:
% 0.39/0.62         ((r1_tarski @ (k1_tarski @ X15) @ X17) | ~ (r2_hidden @ X15 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.39/0.62          | (r1_tarski @ 
% 0.39/0.62             (k1_tarski @ 
% 0.39/0.62              (k4_tarski @ (sk_B @ (k10_relat_1 @ X0 @ X1)) @ 
% 0.39/0.62               (sk_D @ X0 @ X1 @ (sk_B @ (k10_relat_1 @ X0 @ X1))))) @ 
% 0.39/0.62             X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.62  thf(t3_xboole_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.62          | ((k1_tarski @ 
% 0.39/0.62              (k4_tarski @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.39/0.62               (sk_D @ k1_xboole_0 @ X0 @ 
% 0.39/0.62                (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0)))))
% 0.39/0.62              = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.62  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.39/0.62  thf('8', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.39/0.62  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.39/0.62  thf('9', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.62  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((k1_tarski @ 
% 0.39/0.62              (k4_tarski @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.39/0.62               (sk_D @ k1_xboole_0 @ X0 @ 
% 0.39/0.62                (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0)))))
% 0.39/0.62              = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '10'])).
% 0.39/0.62  thf(t20_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.39/0.62         ( k1_tarski @ A ) ) <=>
% 0.39/0.62       ( ( A ) != ( B ) ) ))).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         (((X19) != (X18))
% 0.39/0.62          | ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X18))
% 0.39/0.62              != (k1_tarski @ X19)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X18 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X18))
% 0.39/0.62           != (k1_tarski @ X18))),
% 0.39/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.62  thf(t69_enumset1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.62  thf('14', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf(t12_setfam_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X22 : $i, X23 : $i]:
% 0.39/0.62         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf(t11_setfam_1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.39/0.62  thf('17', plain, (![X21 : $i]: ((k1_setfam_1 @ (k1_tarski @ X21)) = (X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.39/0.62  thf('18', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.62  thf(t100_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ X2)
% 0.39/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.62  thf(t92_xboole_1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.62  thf('21', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.62  thf('22', plain, (![X18 : $i]: ((k1_xboole_0) != (k1_tarski @ X18))),
% 0.39/0.62      inference('demod', [status(thm)], ['13', '20', '21'])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('clc', [status(thm)], ['11', '22'])).
% 0.39/0.62  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '23'])).
% 0.39/0.62  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
