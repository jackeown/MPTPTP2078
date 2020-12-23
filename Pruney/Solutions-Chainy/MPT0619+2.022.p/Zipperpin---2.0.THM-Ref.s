%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1jrrmXw7wj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 158 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  566 (1843 expanded)
%              Number of equality atoms :   69 ( 256 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

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

thf('4',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ X16 )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( X16
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ X16 )
      | ( ( sk_C_1 @ X16 @ X17 )
        = ( k1_funct_1 @ X17 @ ( sk_D_1 @ X16 @ X17 ) ) )
      | ( X16
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ X16 )
      | ( ( sk_C_1 @ X16 @ X17 )
       != ( k1_funct_1 @ X17 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ( X16
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35','36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1jrrmXw7wj
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:40:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 126 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.54  thf(t69_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('0', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf(d2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (((X1) != (X0))
% 0.20/0.54          | (r2_hidden @ X1 @ X2)
% 0.20/0.54          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.54  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.54  thf(t14_funct_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.54         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.54            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.20/0.54  thf('4', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d5_funct_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54               ( ?[D:$i]:
% 0.20/0.54                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.54                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C_1 @ X16 @ X17) @ X16)
% 0.20/0.54          | (r2_hidden @ (sk_D_1 @ X16 @ X17) @ (k1_relat_1 @ X17))
% 0.20/0.54          | ((X16) = (k2_relat_1 @ X17))
% 0.20/0.54          | ~ (v1_funct_1 @ X17)
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54          | ((X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.20/0.54          | ((X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.54  thf('10', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.54          | ((X4) = (X3))
% 0.20/0.54          | ((X4) = (X0))
% 0.20/0.54          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (((X4) = (X0))
% 0.20/0.54          | ((X4) = (X3))
% 0.20/0.54          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0)
% 0.20/0.54          | ((X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ((sk_D_1 @ X0 @ sk_B) = (sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((sk_D_1 @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_C_1 @ X16 @ X17) @ X16)
% 0.20/0.54          | ((sk_C_1 @ X16 @ X17) = (k1_funct_1 @ X17 @ (sk_D_1 @ X16 @ X17)))
% 0.20/0.54          | ((X16) = (k2_relat_1 @ X17))
% 0.20/0.54          | ~ (v1_funct_1 @ X17)
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (v1_funct_1 @ X1)
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ X1)
% 0.20/0.54              = (k1_funct_1 @ X1 @ (sk_D_1 @ (k1_tarski @ X0) @ X1)))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.54  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.54          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.20/0.54      inference('eq_fact', [status(thm)], ['25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.20/0.54        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.54            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.54         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (sk_C_1 @ X16 @ X17) @ X16)
% 0.20/0.54          | ((sk_C_1 @ X16 @ X17) != (k1_funct_1 @ X17 @ X18))
% 0.20/0.54          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.20/0.54          | ((X16) = (k2_relat_1 @ X17))
% 0.20/0.54          | ~ (v1_funct_1 @ X17)
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.20/0.54             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.54          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.54          | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.54          | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.54              != (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.54  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('35', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.20/0.54         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.54          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '32', '33', '34', '35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.54          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('42', plain, ($false), inference('sup-', [status(thm)], ['3', '41'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
