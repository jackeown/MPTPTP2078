%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JiZyuof7ts

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  99 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 ( 686 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ ( k10_relat_1 @ X47 @ X45 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X45 @ X46 ) @ X45 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('17',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('22',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JiZyuof7ts
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 203 iterations in 0.095s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(t3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf(t166_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.55         ( ?[D:$i]:
% 0.20/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X46 @ (k10_relat_1 @ X47 @ X45))
% 0.20/0.55          | (r2_hidden @ (sk_D_1 @ X47 @ X45 @ X46) @ X45)
% 0.20/0.55          | ~ (v1_relat_1 @ X47))),
% 0.20/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r2_hidden @ 
% 0.20/0.55             (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.55  thf('3', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.55  thf(l24_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X38 : $i, X39 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ (k1_tarski @ X38) @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 0.20/0.55      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.55  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.55  thf(d4_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.55  thf(t12_setfam_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X42 : $i, X43 : $i]:
% 0.20/0.55         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.20/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.55         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.20/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.55          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.55          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.55          | ((X1) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.55          | ((X1) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.55          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.55          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((X0) = (k1_xboole_0))
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((X0) = (k1_xboole_0))
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '20'])).
% 0.20/0.55  thf(t171_relat_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( v1_relat_1 @ A ) =>
% 0.20/0.55          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 0.20/0.55  thf('22', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
