%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ww4KsLA3Os

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:33 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  446 ( 664 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t158_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X20 @ X21 ) @ ( k9_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k9_relat_1 @ X23 @ X25 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X1 ) @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X1 ) @ ( k9_relat_1 @ sk_D_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['24','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X1 ) @ ( k9_relat_1 @ sk_D_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ww4KsLA3Os
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.14  % Solved by: fo/fo7.sh
% 0.92/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.14  % done 931 iterations in 0.668s
% 0.92/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.14  % SZS output start Refutation
% 0.92/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.14  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.92/1.14  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.92/1.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.92/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.92/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.14  thf(t158_relat_1, conjecture,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ C ) =>
% 0.92/1.14       ( ![D:$i]:
% 0.92/1.14         ( ( v1_relat_1 @ D ) =>
% 0.92/1.14           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.92/1.14             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.92/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.14        ( ( v1_relat_1 @ C ) =>
% 0.92/1.14          ( ![D:$i]:
% 0.92/1.14            ( ( v1_relat_1 @ D ) =>
% 0.92/1.14              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.92/1.14                ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.92/1.14    inference('cnf.neg', [status(esa)], [t158_relat_1])).
% 0.92/1.14  thf('0', plain,
% 0.92/1.14      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.92/1.14          (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf(d3_tarski, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( r1_tarski @ A @ B ) <=>
% 0.92/1.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.92/1.14  thf('1', plain,
% 0.92/1.14      (![X3 : $i, X5 : $i]:
% 0.92/1.14         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf(d3_xboole_0, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.92/1.14       ( ![D:$i]:
% 0.92/1.14         ( ( r2_hidden @ D @ C ) <=>
% 0.92/1.14           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.92/1.14  thf('2', plain,
% 0.92/1.14      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.92/1.14         (~ (r2_hidden @ X10 @ X8)
% 0.92/1.14          | (r2_hidden @ X10 @ X9)
% 0.92/1.14          | (r2_hidden @ X10 @ X7)
% 0.92/1.14          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.92/1.14  thf('3', plain,
% 0.92/1.14      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.92/1.14         ((r2_hidden @ X10 @ X7)
% 0.92/1.14          | (r2_hidden @ X10 @ X9)
% 0.92/1.14          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X9 @ X7)))),
% 0.92/1.14      inference('simplify', [status(thm)], ['2'])).
% 0.92/1.14  thf('4', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.14         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.92/1.14          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 0.92/1.14          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['1', '3'])).
% 0.92/1.14  thf('5', plain,
% 0.92/1.14      (![X3 : $i, X5 : $i]:
% 0.92/1.14         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf('6', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         ((r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X1)
% 0.92/1.14          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.92/1.14          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['4', '5'])).
% 0.92/1.14  thf('7', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.92/1.14          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X1))),
% 0.92/1.14      inference('simplify', [status(thm)], ['6'])).
% 0.92/1.14  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('9', plain,
% 0.92/1.14      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.92/1.14         (~ (r2_hidden @ X2 @ X3)
% 0.92/1.14          | (r2_hidden @ X2 @ X4)
% 0.92/1.14          | ~ (r1_tarski @ X3 @ X4))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf('10', plain,
% 0.92/1.14      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.92/1.14      inference('sup-', [status(thm)], ['8', '9'])).
% 0.92/1.14  thf('11', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ X0)
% 0.92/1.14          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ sk_A)) @ sk_B))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '10'])).
% 0.92/1.14  thf('12', plain,
% 0.92/1.14      (![X3 : $i, X5 : $i]:
% 0.92/1.14         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.14  thf('13', plain,
% 0.92/1.14      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)
% 0.92/1.14        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B))),
% 0.92/1.14      inference('sup-', [status(thm)], ['11', '12'])).
% 0.92/1.14  thf(commutativity_k2_xboole_0, axiom,
% 0.92/1.14    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.92/1.14  thf('14', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.92/1.14  thf('15', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.92/1.14  thf('16', plain,
% 0.92/1.14      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.92/1.14        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.92/1.14      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.92/1.14  thf('17', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.92/1.14      inference('simplify', [status(thm)], ['16'])).
% 0.92/1.14  thf('18', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.92/1.14  thf(t7_xboole_1, axiom,
% 0.92/1.14    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.92/1.14  thf('19', plain,
% 0.92/1.14      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.92/1.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.92/1.14  thf('20', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.92/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.92/1.14  thf(d10_xboole_0, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.14  thf('21', plain,
% 0.92/1.14      (![X12 : $i, X14 : $i]:
% 0.92/1.14         (((X12) = (X14))
% 0.92/1.14          | ~ (r1_tarski @ X14 @ X12)
% 0.92/1.14          | ~ (r1_tarski @ X12 @ X14))),
% 0.92/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.14  thf('22', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.92/1.14          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['20', '21'])).
% 0.92/1.14  thf('23', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.92/1.14      inference('sup-', [status(thm)], ['17', '22'])).
% 0.92/1.14  thf(t153_relat_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ C ) =>
% 0.92/1.14       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.92/1.14         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.92/1.14  thf('24', plain,
% 0.92/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.14         (((k9_relat_1 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 0.92/1.14            = (k2_xboole_0 @ (k9_relat_1 @ X20 @ X21) @ 
% 0.92/1.14               (k9_relat_1 @ X20 @ X22)))
% 0.92/1.14          | ~ (v1_relat_1 @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.92/1.14  thf('25', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.92/1.14  thf('26', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf(t157_relat_1, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( v1_relat_1 @ B ) =>
% 0.92/1.14       ( ![C:$i]:
% 0.92/1.14         ( ( v1_relat_1 @ C ) =>
% 0.92/1.14           ( ( r1_tarski @ B @ C ) =>
% 0.92/1.14             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.92/1.14  thf('27', plain,
% 0.92/1.14      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ X23)
% 0.92/1.14          | (r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k9_relat_1 @ X23 @ X25))
% 0.92/1.14          | ~ (r1_tarski @ X24 @ X23)
% 0.92/1.14          | ~ (v1_relat_1 @ X24))),
% 0.92/1.14      inference('cnf', [status(esa)], [t157_relat_1])).
% 0.92/1.14  thf('28', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (~ (v1_relat_1 @ sk_C_1)
% 0.92/1.14          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ 
% 0.92/1.14             (k9_relat_1 @ sk_D_1 @ X0))
% 0.92/1.14          | ~ (v1_relat_1 @ sk_D_1))),
% 0.92/1.14      inference('sup-', [status(thm)], ['26', '27'])).
% 0.92/1.14  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('31', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ (k9_relat_1 @ sk_D_1 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.92/1.14  thf(t10_xboole_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.92/1.14  thf('32', plain,
% 0.92/1.14      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.92/1.14         (~ (r1_tarski @ X15 @ X16)
% 0.92/1.14          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.92/1.14  thf('33', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ 
% 0.92/1.14          (k2_xboole_0 @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['31', '32'])).
% 0.92/1.14  thf('34', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X1) @ 
% 0.92/1.14          (k2_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X1) @ X0))),
% 0.92/1.14      inference('sup+', [status(thm)], ['25', '33'])).
% 0.92/1.14  thf('35', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ X1) @ 
% 0.92/1.14           (k9_relat_1 @ sk_D_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.92/1.14          | ~ (v1_relat_1 @ sk_D_1))),
% 0.92/1.14      inference('sup+', [status(thm)], ['24', '34'])).
% 0.92/1.14  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('37', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X1) @ 
% 0.92/1.14          (k9_relat_1 @ sk_D_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.92/1.14      inference('demod', [status(thm)], ['35', '36'])).
% 0.92/1.14  thf('38', plain,
% 0.92/1.14      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.92/1.14      inference('sup+', [status(thm)], ['23', '37'])).
% 0.92/1.14  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.92/1.14  
% 0.92/1.14  % SZS output end Refutation
% 0.92/1.14  
% 0.92/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
