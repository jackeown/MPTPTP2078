%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D07YT0L61a

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 128 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  508 (1542 expanded)
%              Number of equality atoms :   61 ( 202 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X7 @ X8 ) @ X7 )
      | ( ( sk_C_2 @ X7 @ X8 )
        = ( k1_funct_1 @ X8 @ ( sk_D @ X7 @ X8 ) ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('16',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X7 @ X8 ) @ X7 )
      | ( ( sk_C_2 @ X7 @ X8 )
       != ( k1_funct_1 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D07YT0L61a
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 69 iterations in 0.061s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(t14_funct_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.56         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i]:
% 0.21/0.56        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.56            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.21/0.56  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d1_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.56  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.56  thf('3', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.56  thf(d5_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.56               ( ?[D:$i]:
% 0.21/0.56                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.56                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ X7 @ X8) @ X7)
% 0.21/0.56          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.21/0.56          | ((X7) = (k2_relat_1 @ X8))
% 0.21/0.56          | ~ (v1_funct_1 @ X8)
% 0.21/0.56          | ~ (v1_relat_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.56  thf('5', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X3 : $i]:
% 0.21/0.56         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ sk_B)
% 0.21/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56          | ((X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0)
% 0.21/0.56          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.56  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B) @ X0)
% 0.21/0.56          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i, X3 : $i]:
% 0.21/0.56         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ X7 @ X8) @ X7)
% 0.21/0.56          | ((sk_C_2 @ X7 @ X8) = (k1_funct_1 @ X8 @ (sk_D @ X7 @ X8)))
% 0.21/0.56          | ((X7) = (k2_relat_1 @ X8))
% 0.21/0.56          | ~ (v1_funct_1 @ X8)
% 0.21/0.56          | ~ (v1_relat_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X3 : $i]:
% 0.21/0.56         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X1)
% 0.21/0.56          | ~ (v1_funct_1 @ X1)
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ X1)
% 0.21/0.56              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['14', '17'])).
% 0.21/0.56  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.21/0.56          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.21/0.56      inference('eq_fact', [status(thm)], ['22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.21/0.56        | ((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.21/0.56            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.21/0.56         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (~ (r2_hidden @ (sk_C_2 @ X7 @ X8) @ X7)
% 0.21/0.56          | ((sk_C_2 @ X7 @ X8) != (k1_funct_1 @ X8 @ X9))
% 0.21/0.56          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.21/0.56          | ((X7) = (k2_relat_1 @ X8))
% 0.21/0.56          | ~ (v1_funct_1 @ X8)
% 0.21/0.56          | ~ (v1_relat_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.21/0.56             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.21/0.56          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56          | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.21/0.56          | ((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.21/0.56              != (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.56  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((sk_C_2 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.21/0.56         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.21/0.56          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.21/0.56          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.56  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain, ($false), inference('sup-', [status(thm)], ['3', '37'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
