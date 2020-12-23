%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OlQb27EgAV

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 100 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  476 ( 772 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X24 @ X25 ) @ ( sk_D @ X24 @ X25 ) ) @ X25 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X24 @ X25 ) @ ( sk_D @ X24 @ X25 ) ) @ X24 )
      | ( X25 = X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X31 @ X32 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ( zip_tseitin_0 @ X8 @ X7 @ X6 )
      | ( zip_tseitin_1 @ X8 @ X7 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_A = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( zip_tseitin_0 @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 @ X0 )
      | ( zip_tseitin_1 @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( zip_tseitin_1 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_0 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_0 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( zip_tseitin_1 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_0 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( zip_tseitin_1 @ X3 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,
    ( ( zip_tseitin_0 @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OlQb27EgAV
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 43 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(d2_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( ( A ) = ( B ) ) <=>
% 0.20/0.48             ( ![C:$i,D:$i]:
% 0.20/0.48               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.20/0.48                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X24 : $i, X25 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X24)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X24 @ X25) @ (sk_D @ X24 @ X25)) @ X25)
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X24 @ X25) @ (sk_D @ X24 @ X25)) @ X24)
% 0.20/0.48          | ((X25) = (X24))
% 0.20/0.48          | ~ (v1_relat_1 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.20/0.48  thf(t56_relat_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.20/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ A ) =>
% 0.20/0.48          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.20/0.48            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i]: ~ (r2_hidden @ (k4_tarski @ X31 @ X32) @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_A)
% 0.20/0.48          | ((sk_A) = (X0))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) = (X0))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('6', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.20/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.48  thf(t37_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X16 : $i, X18 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ X16 @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.20/0.48  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X19 : $i, X21 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) = (X0))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t21_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.48  thf(t22_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.48  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(t5_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.20/0.48          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.48          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_2, axiom,
% 0.20/0.48    (![C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.48       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_4, axiom,
% 0.20/0.48    (![C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.48       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_5, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.20/0.48          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.20/0.48          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.48          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X6 @ X7)
% 0.20/0.48          | (zip_tseitin_0 @ X8 @ X7 @ X6)
% 0.20/0.48          | (zip_tseitin_1 @ X8 @ X7 @ X6)
% 0.20/0.48          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.48          | (zip_tseitin_1 @ X1 @ X0 @ X0)
% 0.20/0.48          | (zip_tseitin_0 @ X1 @ X0 @ X0)
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((sk_A) = (X0))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.48          | (zip_tseitin_0 @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0 @ X0)
% 0.20/0.48          | (zip_tseitin_1 @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((zip_tseitin_1 @ 
% 0.20/0.48         (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48         k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | (zip_tseitin_0 @ 
% 0.20/0.48           (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48           k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '18'])).
% 0.20/0.48  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(fc2_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X29 : $i, X30 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k4_xboole_0 @ X29 @ X30)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((zip_tseitin_1 @ 
% 0.20/0.48         (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48         k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | (zip_tseitin_0 @ 
% 0.20/0.48           (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48           k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.20/0.48  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((zip_tseitin_1 @ 
% 0.20/0.48         (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48         k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | (zip_tseitin_0 @ 
% 0.20/0.48           (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.20/0.48            (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48           k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ X5) | ~ (zip_tseitin_1 @ X3 @ X5 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((zip_tseitin_0 @ 
% 0.20/0.48         (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48         k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | ~ (r2_hidden @ 
% 0.20/0.48             (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.20/0.48              (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48             k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X2) | ~ (zip_tseitin_0 @ X0 @ X1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (~ (r2_hidden @ 
% 0.20/0.48          (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.20/0.48           (sk_D @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.48          k1_xboole_0)),
% 0.20/0.48      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain, ((~ (v1_relat_1 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '31'])).
% 0.20/0.48  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.48  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
