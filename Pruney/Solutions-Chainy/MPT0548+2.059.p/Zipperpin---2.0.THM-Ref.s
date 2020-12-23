%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w2dOSGnwbz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:10 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   54 (  54 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  319 ( 319 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
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

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ ( k9_relat_1 @ X47 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X47 @ X45 @ X46 ) @ X46 ) @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ ( sk_B @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) @ X0 ) ) ),
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
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
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
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','21'])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w2dOSGnwbz
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:35:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 354 iterations in 0.157s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.62  thf(t150_relat_1, conjecture,
% 0.40/0.62    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.40/0.62  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t7_xboole_0, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.62  thf(t143_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ C ) =>
% 0.40/0.62       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.40/0.62         ( ?[D:$i]:
% 0.40/0.62           ( ( r2_hidden @ D @ B ) & 
% 0.40/0.62             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.40/0.62             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X46 @ (k9_relat_1 @ X47 @ X45))
% 0.40/0.62          | (r2_hidden @ (k4_tarski @ (sk_D @ X47 @ X45 @ X46) @ X46) @ X47)
% 0.40/0.62          | ~ (v1_relat_1 @ X47))),
% 0.40/0.62      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | (r2_hidden @ 
% 0.40/0.62             (k4_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.40/0.62              (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.40/0.62             X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf(l1_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X33 : $i, X35 : $i]:
% 0.40/0.62         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.40/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((k9_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.40/0.62          | (r1_tarski @ 
% 0.40/0.62             (k1_tarski @ 
% 0.40/0.62              (k4_tarski @ 
% 0.40/0.62               (sk_D @ X0 @ X1 @ (sk_B @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.40/0.62               (sk_B @ (k9_relat_1 @ X0 @ X1)))) @ 
% 0.40/0.62             X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf(t3_xboole_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.62          | ((k1_tarski @ 
% 0.40/0.62              (k4_tarski @ 
% 0.40/0.62               (sk_D @ k1_xboole_0 @ X0 @ 
% 0.40/0.62                (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.40/0.62               (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0))))
% 0.40/0.62              = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.62  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.40/0.62  thf('8', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.40/0.62  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.40/0.62  thf('9', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.40/0.62  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.62          | ((k1_tarski @ 
% 0.40/0.62              (k4_tarski @ 
% 0.40/0.62               (sk_D @ k1_xboole_0 @ X0 @ 
% 0.40/0.62                (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.40/0.62               (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0))))
% 0.40/0.62              = (k1_xboole_0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['7', '10'])).
% 0.40/0.62  thf(t69_enumset1, axiom,
% 0.40/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.62  thf('12', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.62  thf(t20_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.62         ( k1_tarski @ A ) ) <=>
% 0.40/0.62       ( ( A ) != ( B ) ) ))).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X38 : $i, X39 : $i]:
% 0.40/0.62         (((X39) != (X38))
% 0.40/0.62          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 0.40/0.62              != (k1_tarski @ X39)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X38 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 0.40/0.62           != (k1_tarski @ X38))),
% 0.40/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.40/0.62           != (k1_tarski @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.40/0.62  thf(t19_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.40/0.62       ( k1_tarski @ A ) ))).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X36 : $i, X37 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))
% 0.40/0.62           = (k1_tarski @ X36))),
% 0.40/0.62      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.40/0.62  thf(t100_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X1 : $i, X2 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X1 @ X2)
% 0.40/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.40/0.62           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.62  thf(t92_xboole_1, axiom,
% 0.40/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.62  thf('19', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.40/0.62           = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '20'])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('clc', [status(thm)], ['11', '21'])).
% 0.40/0.62  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['0', '22'])).
% 0.40/0.62  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
