%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ImvFmYb6v5

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:09 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   55 (  69 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  438 ( 592 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_D @ X3 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','16'])).

thf(t141_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_xboole_0 @ B @ C )
         => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_xboole_0 @ B @ C )
           => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t141_funct_1])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X16 @ X17 ) @ ( k10_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('22',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ImvFmYb6v5
% 0.12/0.35  % Computer   : n007.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 11:19:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 152 iterations in 0.208s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(d4_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.67       ( ![D:$i]:
% 0.46/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.67           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.46/0.67         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.46/0.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.46/0.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.67  thf(t166_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.46/0.67         ( ?[D:$i]:
% 0.46/0.67           ( ( r2_hidden @ D @ B ) & 
% 0.46/0.67             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.46/0.67             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.46/0.67          | (r2_hidden @ (sk_D_1 @ X15 @ X13 @ X14) @ X13)
% 0.46/0.67          | ~ (v1_relat_1 @ X15))),
% 0.46/0.67      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((r2_hidden @ (sk_D @ X3 @ (k10_relat_1 @ X1 @ X0) @ X2) @ X3)
% 0.46/0.67          | ((X3) = (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X1)
% 0.46/0.67          | (r2_hidden @ 
% 0.46/0.67             (sk_D_1 @ X1 @ X0 @ (sk_D @ X3 @ (k10_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.46/0.67             X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.67  thf('3', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.67  thf(l24_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ (k1_tarski @ X10) @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.46/0.67  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X1)
% 0.46/0.67          | ((X2) = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ k1_xboole_0)))
% 0.46/0.67          | (r2_hidden @ (sk_D @ X2 @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X0) @ 
% 0.46/0.67             X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '5'])).
% 0.46/0.67  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k1_xboole_0)
% 0.46/0.67            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ k1_xboole_0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.46/0.67         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.46/0.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.46/0.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.46/0.67          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.67      inference('eq_fact', [status(thm)], ['9'])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.46/0.67         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.46/0.67          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.46/0.67          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.46/0.67          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.46/0.67          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.46/0.67          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.46/0.67          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.46/0.67          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.46/0.67         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.46/0.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.46/0.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.46/0.67          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.67      inference('eq_fact', [status(thm)], ['14'])).
% 0.46/0.67  thf('16', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.67      inference('clc', [status(thm)], ['13', '15'])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['8', '16'])).
% 0.46/0.67  thf(t141_funct_1, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ![B:$i,C:$i]:
% 0.46/0.67         ( ( r1_xboole_0 @ B @ C ) =>
% 0.46/0.67           ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67          ( ![B:$i,C:$i]:
% 0.46/0.67            ( ( r1_xboole_0 @ B @ C ) =>
% 0.46/0.67              ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t141_funct_1])).
% 0.46/0.67  thf('18', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d7_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.67       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i]:
% 0.46/0.67         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.46/0.67      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.67  thf('20', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf(t137_funct_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.46/0.67         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.67         (((k10_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18))
% 0.46/0.67            = (k3_xboole_0 @ (k10_relat_1 @ X16 @ X17) @ 
% 0.46/0.67               (k10_relat_1 @ X16 @ X18)))
% 0.46/0.67          | ~ (v1_funct_1 @ X16)
% 0.46/0.67          | ~ (v1_relat_1 @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X6 : $i, X8 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         (((k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.46/0.67          | ~ (v1_relat_1 @ X2)
% 0.46/0.67          | ~ (v1_funct_1 @ X2)
% 0.46/0.67          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k10_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.46/0.67             (k10_relat_1 @ X0 @ sk_C))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['20', '23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.46/0.67             (k10_relat_1 @ X0 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['17', '24'])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ X0 @ sk_C))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['25'])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (~ (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_B) @ 
% 0.46/0.67          (k10_relat_1 @ sk_A @ sk_C))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('28', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('31', plain, ($false),
% 0.46/0.67      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.53/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
