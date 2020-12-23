%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UCE403MZIj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:12 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   65 (  89 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   19
%              Number of atoms          :  513 ( 760 expanded)
%              Number of equality atoms :   18 (  44 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( sk_C @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( sk_C @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X20 ) @ X23 )
      | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ X23 ) )
      | ( r2_hidden @ X22 @ ( k10_relat_1 @ X23 @ X21 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UCE403MZIj
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:18:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 237 iterations in 0.100s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.23/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.55  thf(t3_xboole_0, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.55  thf('0', plain,
% 0.23/0.55      (![X4 : $i, X5 : $i]:
% 0.23/0.55         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.55  thf(d3_tarski, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.55  thf('1', plain,
% 0.23/0.55      (![X1 : $i, X3 : $i]:
% 0.23/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      (![X1 : $i, X3 : $i]:
% 0.23/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf(t174_relat_1, conjecture,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ B ) =>
% 0.23/0.55       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.55            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.23/0.55            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i,B:$i]:
% 0.23/0.55        ( ( v1_relat_1 @ B ) =>
% 0.23/0.55          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.55               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.23/0.55               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.23/0.55  thf('3', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.55          | (r2_hidden @ X0 @ X2)
% 0.23/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.55  thf(t146_relat_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ A ) =>
% 0.23/0.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (![X19 : $i]:
% 0.23/0.55         (((k9_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (k2_relat_1 @ X19))
% 0.23/0.55          | ~ (v1_relat_1 @ X19))),
% 0.23/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.23/0.55  thf(t143_relat_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ C ) =>
% 0.23/0.55       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.23/0.55         ( ?[D:$i]:
% 0.23/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.23/0.55             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.23/0.55             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.23/0.55          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 0.23/0.55          | ~ (v1_relat_1 @ X18))),
% 0.23/0.55      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r2_hidden @ 
% 0.23/0.55           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ X0)
% 0.23/0.55          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ sk_B)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (k4_tarski @ 
% 0.23/0.55              (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55              (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['7', '11'])).
% 0.23/0.55  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (k4_tarski @ 
% 0.23/0.55              (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55              (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.55  thf(t166_relat_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ C ) =>
% 0.23/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.23/0.55         ( ?[D:$i]:
% 0.23/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.23/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.23/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X20 @ X21)
% 0.23/0.55          | ~ (r2_hidden @ (k4_tarski @ X22 @ X20) @ X23)
% 0.23/0.55          | ~ (r2_hidden @ X20 @ (k2_relat_1 @ X23))
% 0.23/0.55          | (r2_hidden @ X22 @ (k10_relat_1 @ X23 @ X21))
% 0.23/0.55          | ~ (v1_relat_1 @ X23))),
% 0.23/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.23/0.55  thf('16', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | ~ (v1_relat_1 @ sk_B)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             (k10_relat_1 @ sk_B @ X1))
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.55  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('18', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             (k10_relat_1 @ sk_B @ X1))
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.23/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             (k10_relat_1 @ sk_B @ X1))
% 0.23/0.55          | (r1_tarski @ sk_A @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['6', '18'])).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r2_hidden @ 
% 0.23/0.55           (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55           (k10_relat_1 @ sk_B @ X1))
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.23/0.55          | (r1_tarski @ sk_A @ X0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.23/0.55  thf('21', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             (k10_relat_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['1', '20'])).
% 0.23/0.55  thf('22', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('23', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r1_tarski @ sk_A @ X0)
% 0.23/0.55          | (r2_hidden @ 
% 0.23/0.55             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55             k1_xboole_0))),
% 0.23/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.23/0.55  thf('24', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r2_hidden @ 
% 0.23/0.55           (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.23/0.55           k1_xboole_0)
% 0.23/0.55          | (r1_tarski @ sk_A @ X0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.55  thf(t113_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      (![X11 : $i, X12 : $i]:
% 0.23/0.55         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.23/0.55          | ((X12) != (k1_xboole_0)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.55  thf(t152_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.23/0.55      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.23/0.55  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.55  thf('29', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.23/0.55      inference('clc', [status(thm)], ['24', '28'])).
% 0.23/0.55  thf('30', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.55          | (r2_hidden @ X0 @ X2)
% 0.23/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ X1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['0', '31'])).
% 0.23/0.55  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.55  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.23/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.55  thf(t66_xboole_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.23/0.55       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.55  thf('35', plain,
% 0.23/0.55      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 0.23/0.55      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.23/0.55  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.55  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('38', plain, ($false),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
