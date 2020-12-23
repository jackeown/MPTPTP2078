%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tOTyRbXaig

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  417 ( 762 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_D @ X10 @ X11 @ X12 ) @ X10 )
      | ( r2_hidden @ ( sk_E @ X10 @ X11 @ X12 ) @ X11 )
      | ( X10
        = ( k10_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('6',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_A
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ sk_A @ X1 @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ ( sk_D @ sk_A @ X1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A )
      | ( r2_hidden @ ( sk_E @ sk_A @ X1 @ X0 ) @ X1 )
      | ( sk_A
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_A
        = ( k10_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_E @ sk_A @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A )
      | ( sk_A
        = ( k10_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_A
        = ( k10_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k10_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( sk_C_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k10_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_D @ X10 @ X11 @ X12 ) @ X10 )
      | ( r2_hidden @ ( sk_E @ X10 @ X11 @ X12 ) @ X11 )
      | ( X10
        = ( k10_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('25',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X22: $i] :
      ~ ( r2_hidden @ X22 @ sk_A ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k10_relat_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k10_relat_1 @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_A @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tOTyRbXaig
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 159 iterations in 0.095s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(fc3_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.54  thf('0', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.54  thf(t3_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.54  thf(t7_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.54          ( ![C:$i]:
% 0.21/0.54            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8) @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(d14_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i,C:$i]:
% 0.21/0.54         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.21/0.54           ( ![D:$i]:
% 0.21/0.54             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54               ( ?[E:$i]:
% 0.21/0.54                 ( ( r2_hidden @ E @ B ) & 
% 0.21/0.54                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_D @ X10 @ X11 @ X12) @ X10)
% 0.21/0.54          | (r2_hidden @ (sk_E @ X10 @ X11 @ X12) @ X11)
% 0.21/0.54          | ((X10) = (k10_relat_1 @ X12 @ X11))
% 0.21/0.54          | ~ (v1_relat_1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.21/0.54  thf(t1_mcart_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54             ( ![B:$i]:
% 0.21/0.54               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((sk_A) = (k10_relat_1 @ X0 @ X1))
% 0.21/0.54          | (r2_hidden @ (sk_E @ sk_A @ X1 @ X0) @ X1)
% 0.21/0.54          | ~ (r1_xboole_0 @ (sk_D @ sk_A @ X1 @ X0) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)
% 0.21/0.54          | (r2_hidden @ (sk_E @ sk_A @ X1 @ X0) @ X1)
% 0.21/0.54          | ((sk_A) = (k10_relat_1 @ X0 @ X1))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((sk_A) = (k10_relat_1 @ X0 @ sk_A))
% 0.21/0.55          | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)
% 0.21/0.55          | ~ (r1_xboole_0 @ (sk_E @ sk_A @ sk_A @ X0) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)
% 0.21/0.55          | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)
% 0.21/0.55          | ((sk_A) = (k10_relat_1 @ X0 @ sk_A))
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((sk_A) = (k10_relat_1 @ X0 @ sk_A))
% 0.21/0.55          | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_A) = (k10_relat_1 @ X0 @ sk_A))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X9 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X9 @ (sk_C_1 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.55      inference('condensation', [status(thm)], ['17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.21/0.55          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '19'])).
% 0.21/0.55  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i]: (((sk_A) = (k10_relat_1 @ X0 @ sk_A)) | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '21'])).
% 0.21/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.55  thf('23', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ X10 @ X11 @ X12) @ X10)
% 0.21/0.55          | (r2_hidden @ (sk_E @ X10 @ X11 @ X12) @ X11)
% 0.21/0.55          | ((X10) = (k10_relat_1 @ X12 @ X11))
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain, (![X22 : $i]: ~ (r2_hidden @ X22 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((X1) = (k10_relat_1 @ X0 @ sk_A))
% 0.21/0.55          | (r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '31'])).
% 0.21/0.55  thf(t7_ordinal1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k10_relat_1 @ X1 @ sk_A))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ sk_A @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0) | ((k1_xboole_0) = (k10_relat_1 @ X0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_xboole_0) = (sk_A)) | ~ (v1_relat_1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ((k1_xboole_0) = (sk_A)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.55  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('39', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, ($false), inference('sup-', [status(thm)], ['0', '39'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
