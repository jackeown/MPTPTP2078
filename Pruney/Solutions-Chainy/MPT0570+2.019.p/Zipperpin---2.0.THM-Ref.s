%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GhjUxUdDlK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:10 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   65 (  83 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   19
%              Number of atoms          :  522 ( 726 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
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

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k7_relat_1 @ X26 @ X27 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X16 @ X14 @ X15 ) @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( sk_C @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( sk_C @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X22 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X22 ) )
      | ( r2_hidden @ X21 @ ( k10_relat_1 @ X22 @ X20 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ ( k1_relat_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) @ k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['29','33'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GhjUxUdDlK
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.82  % Solved by: fo/fo7.sh
% 0.61/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.82  % done 307 iterations in 0.365s
% 0.61/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.82  % SZS output start Refutation
% 0.61/0.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.61/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.61/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.61/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.82  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.61/0.82  thf(d3_tarski, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.82  thf('0', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('1', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf(t174_relat_1, conjecture,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ B ) =>
% 0.61/0.82       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.61/0.82            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.61/0.82            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.82    (~( ![A:$i,B:$i]:
% 0.61/0.82        ( ( v1_relat_1 @ B ) =>
% 0.61/0.82          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.61/0.82               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.61/0.82               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.61/0.82    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.61/0.82  thf('2', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('3', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.82          | (r2_hidden @ X0 @ X2)
% 0.61/0.82          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('4', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['1', '4'])).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['1', '4'])).
% 0.61/0.82  thf(d10_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.82  thf('7', plain,
% 0.61/0.82      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.61/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.82  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.61/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.61/0.82  thf(t97_relat_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ B ) =>
% 0.61/0.82       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.61/0.82         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.61/0.82  thf('9', plain,
% 0.61/0.82      (![X26 : $i, X27 : $i]:
% 0.61/0.82         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.61/0.82          | ((k7_relat_1 @ X26 @ X27) = (X26))
% 0.61/0.82          | ~ (v1_relat_1 @ X26))),
% 0.61/0.82      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.61/0.82  thf('10', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.82  thf(t148_relat_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ B ) =>
% 0.61/0.82       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (![X17 : $i, X18 : $i]:
% 0.61/0.82         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.61/0.82          | ~ (v1_relat_1 @ X17))),
% 0.61/0.82      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.61/0.82  thf('12', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.61/0.82          | ~ (v1_relat_1 @ X0)
% 0.61/0.82          | ~ (v1_relat_1 @ X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('13', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (v1_relat_1 @ X0)
% 0.61/0.82          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.61/0.82      inference('simplify', [status(thm)], ['12'])).
% 0.61/0.82  thf(t143_relat_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ C ) =>
% 0.61/0.82       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.61/0.82         ( ?[D:$i]:
% 0.61/0.82           ( ( r2_hidden @ D @ B ) & 
% 0.61/0.82             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.61/0.82             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.61/0.82  thf('14', plain,
% 0.61/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.61/0.82          | (r2_hidden @ (k4_tarski @ (sk_D @ X16 @ X14 @ X15) @ X15) @ X16)
% 0.61/0.82          | ~ (v1_relat_1 @ X16))),
% 0.61/0.82      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.61/0.82  thf('15', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.61/0.82          | ~ (v1_relat_1 @ X0)
% 0.61/0.82          | ~ (v1_relat_1 @ X0)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.82  thf('16', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((r2_hidden @ 
% 0.61/0.82           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.61/0.82          | ~ (v1_relat_1 @ X0)
% 0.61/0.82          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['15'])).
% 0.61/0.82  thf('17', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | ~ (v1_relat_1 @ sk_B)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (k4_tarski @ 
% 0.61/0.82              (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82              (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['6', '16'])).
% 0.61/0.82  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('19', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (k4_tarski @ 
% 0.61/0.82              (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82              (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['17', '18'])).
% 0.61/0.82  thf(t166_relat_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ C ) =>
% 0.61/0.82       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.61/0.82         ( ?[D:$i]:
% 0.61/0.82           ( ( r2_hidden @ D @ B ) & 
% 0.61/0.82             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.61/0.82             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.61/0.82  thf('20', plain,
% 0.61/0.82      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X19 @ X20)
% 0.61/0.82          | ~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X22)
% 0.61/0.82          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ X22))
% 0.61/0.82          | (r2_hidden @ X21 @ (k10_relat_1 @ X22 @ X20))
% 0.61/0.82          | ~ (v1_relat_1 @ X22))),
% 0.61/0.82      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.61/0.82  thf('21', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | ~ (v1_relat_1 @ sk_B)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             (k10_relat_1 @ sk_B @ X1))
% 0.61/0.82          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.61/0.82          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.61/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.61/0.82  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('23', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             (k10_relat_1 @ sk_B @ X1))
% 0.61/0.82          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.61/0.82          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.61/0.82      inference('demod', [status(thm)], ['21', '22'])).
% 0.61/0.82  thf('24', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             (k10_relat_1 @ sk_B @ X1))
% 0.61/0.82          | (r1_tarski @ sk_A @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['5', '23'])).
% 0.61/0.82  thf('25', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((r2_hidden @ 
% 0.61/0.82           (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82           (k10_relat_1 @ sk_B @ X1))
% 0.61/0.82          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.61/0.82          | (r1_tarski @ sk_A @ X0))),
% 0.61/0.82      inference('simplify', [status(thm)], ['24'])).
% 0.61/0.82  thf('26', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             (k10_relat_1 @ sk_B @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['0', '25'])).
% 0.61/0.82  thf('27', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('28', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r1_tarski @ sk_A @ X0)
% 0.61/0.82          | (r2_hidden @ 
% 0.61/0.82             (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82             k1_xboole_0))),
% 0.61/0.82      inference('demod', [status(thm)], ['26', '27'])).
% 0.61/0.82  thf('29', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r2_hidden @ 
% 0.61/0.82           (sk_D @ sk_B @ (k1_relat_1 @ sk_B) @ (sk_C @ X0 @ sk_A)) @ 
% 0.61/0.82           k1_xboole_0)
% 0.61/0.82          | (r1_tarski @ sk_A @ X0))),
% 0.61/0.82      inference('simplify', [status(thm)], ['28'])).
% 0.61/0.82  thf(t113_zfmisc_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.61/0.82  thf('30', plain,
% 0.61/0.82      (![X9 : $i, X10 : $i]:
% 0.61/0.82         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.61/0.82  thf('31', plain,
% 0.61/0.82      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.82      inference('simplify', [status(thm)], ['30'])).
% 0.61/0.82  thf(t152_zfmisc_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.61/0.82  thf('32', plain,
% 0.61/0.82      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.61/0.82  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.61/0.82      inference('sup-', [status(thm)], ['31', '32'])).
% 0.61/0.82  thf('34', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.61/0.82      inference('clc', [status(thm)], ['29', '33'])).
% 0.61/0.82  thf(t3_xboole_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.82  thf('35', plain,
% 0.61/0.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.61/0.82  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.82  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('38', plain, ($false),
% 0.61/0.82      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
