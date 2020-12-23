%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d8KZYAnMy1

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  374 ( 539 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

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

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

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
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
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
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d8KZYAnMy1
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:00:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 134 iterations in 0.090s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.53  thf(t137_funct_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.53       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.19/0.53         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17))
% 0.19/0.53            = (k3_xboole_0 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.19/0.53               (k10_relat_1 @ X15 @ X17)))
% 0.19/0.53          | ~ (v1_funct_1 @ X15)
% 0.19/0.53          | ~ (v1_relat_1 @ X15))),
% 0.19/0.53      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.19/0.53  thf(t3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf(t166_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.19/0.53         ( ?[D:$i]:
% 0.19/0.53           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.53             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.19/0.53             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X13 @ (k10_relat_1 @ X14 @ X12))
% 0.19/0.53          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.19/0.53          | ~ (v1_relat_1 @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | (r2_hidden @ 
% 0.19/0.53             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.53  thf('4', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.53  thf(t55_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X8 @ X9) @ X10)
% 0.19/0.53          | ~ (r2_hidden @ X8 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.19/0.53  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.19/0.53  thf(d7_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X1)
% 0.19/0.53          | ((k3_xboole_0 @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 0.19/0.53              = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.19/0.53            = (k1_xboole_0))
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ~ (v1_funct_1 @ X1)
% 0.19/0.53          | ~ (v1_relat_1 @ X1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['0', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.53  thf('13', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X1 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ~ (v1_funct_1 @ X1)
% 0.19/0.53          | ~ (v1_relat_1 @ X1))),
% 0.19/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X1 : $i]:
% 0.19/0.53         (~ (v1_funct_1 @ X1)
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.53  thf(t141_funct_1, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.53       ( ![B:$i,C:$i]:
% 0.19/0.53         ( ( r1_xboole_0 @ B @ C ) =>
% 0.19/0.53           ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.53          ( ![B:$i,C:$i]:
% 0.19/0.53            ( ( r1_xboole_0 @ B @ C ) =>
% 0.19/0.53              ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t141_funct_1])).
% 0.19/0.53  thf('18', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('20', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17))
% 0.19/0.53            = (k3_xboole_0 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.19/0.53               (k10_relat_1 @ X15 @ X17)))
% 0.19/0.53          | ~ (v1_funct_1 @ X15)
% 0.19/0.53          | ~ (v1_relat_1 @ X15))),
% 0.19/0.53      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i, X2 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.19/0.53          | ~ (v1_relat_1 @ X2)
% 0.19/0.53          | ~ (v1_funct_1 @ X2)
% 0.19/0.53          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.53          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.19/0.53             (k10_relat_1 @ X0 @ sk_C_1))
% 0.19/0.53          | ~ (v1_funct_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['20', '23'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_funct_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_funct_1 @ X0)
% 0.19/0.53          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.19/0.53             (k10_relat_1 @ X0 @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['17', '24'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.19/0.53           (k10_relat_1 @ X0 @ sk_C_1))
% 0.19/0.53          | ~ (v1_funct_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (~ (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_B) @ 
% 0.19/0.53          (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('28', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.53  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('31', plain, ($false),
% 0.19/0.53      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
