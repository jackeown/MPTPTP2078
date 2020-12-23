%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IPlmlIdtMN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:55 EST 2020

% Result     : Theorem 4.06s
% Output     : Refutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   44 (  83 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  402 ( 846 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ ( sk_D @ X17 @ X13 ) )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X13 ) @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('8',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X13 ) @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('9',plain,(
    ! [X13: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X18 )
      | ~ ( r2_hidden @ X18 @ X13 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X13: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X18 )
      | ~ ( r2_hidden @ X18 @ X13 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IPlmlIdtMN
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.06/4.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.06/4.28  % Solved by: fo/fo7.sh
% 4.06/4.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.06/4.28  % done 585 iterations in 3.831s
% 4.06/4.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.06/4.28  % SZS output start Refutation
% 4.06/4.28  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 4.06/4.28  thf(sk_A_type, type, sk_A: $i).
% 4.06/4.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.06/4.28  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 4.06/4.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.06/4.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.06/4.28  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.06/4.28  thf(t99_zfmisc_1, conjecture,
% 4.06/4.28    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 4.06/4.28  thf(zf_stmt_0, negated_conjecture,
% 4.06/4.28    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 4.06/4.28    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 4.06/4.28  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 4.06/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.06/4.28  thf(d4_tarski, axiom,
% 4.06/4.28    (![A:$i,B:$i]:
% 4.06/4.28     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 4.06/4.28       ( ![C:$i]:
% 4.06/4.28         ( ( r2_hidden @ C @ B ) <=>
% 4.06/4.28           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 4.06/4.28  thf('1', plain,
% 4.06/4.28      (![X13 : $i, X17 : $i]:
% 4.06/4.28         (((X17) = (k3_tarski @ X13))
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X17 @ X13) @ (sk_D @ X17 @ X13))
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X17))),
% 4.06/4.28      inference('cnf', [status(esa)], [d4_tarski])).
% 4.06/4.28  thf(d10_xboole_0, axiom,
% 4.06/4.28    (![A:$i,B:$i]:
% 4.06/4.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.06/4.28  thf('2', plain,
% 4.06/4.28      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.06/4.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.06/4.28  thf('3', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.06/4.28      inference('simplify', [status(thm)], ['2'])).
% 4.06/4.28  thf(d1_zfmisc_1, axiom,
% 4.06/4.28    (![A:$i,B:$i]:
% 4.06/4.28     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 4.06/4.28       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 4.06/4.28  thf('4', plain,
% 4.06/4.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.06/4.28         (~ (r1_tarski @ X7 @ X8)
% 4.06/4.28          | (r2_hidden @ X7 @ X9)
% 4.06/4.28          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 4.06/4.28      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.06/4.28  thf('5', plain,
% 4.06/4.28      (![X7 : $i, X8 : $i]:
% 4.06/4.28         ((r2_hidden @ X7 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X7 @ X8))),
% 4.06/4.28      inference('simplify', [status(thm)], ['4'])).
% 4.06/4.28  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.06/4.28      inference('sup-', [status(thm)], ['3', '5'])).
% 4.06/4.28  thf('7', plain,
% 4.06/4.28      (![X13 : $i, X17 : $i]:
% 4.06/4.28         (((X17) = (k3_tarski @ X13))
% 4.06/4.28          | (r2_hidden @ (sk_D @ X17 @ X13) @ X13)
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X17))),
% 4.06/4.28      inference('cnf', [status(esa)], [d4_tarski])).
% 4.06/4.28  thf('8', plain,
% 4.06/4.28      (![X13 : $i, X17 : $i]:
% 4.06/4.28         (((X17) = (k3_tarski @ X13))
% 4.06/4.28          | (r2_hidden @ (sk_D @ X17 @ X13) @ X13)
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X17))),
% 4.06/4.28      inference('cnf', [status(esa)], [d4_tarski])).
% 4.06/4.28  thf('9', plain,
% 4.06/4.28      (![X13 : $i, X17 : $i, X18 : $i]:
% 4.06/4.28         (((X17) = (k3_tarski @ X13))
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X18)
% 4.06/4.28          | ~ (r2_hidden @ X18 @ X13)
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X17))),
% 4.06/4.28      inference('cnf', [status(esa)], [d4_tarski])).
% 4.06/4.28  thf('10', plain,
% 4.06/4.28      (![X0 : $i, X1 : $i]:
% 4.06/4.28         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 4.06/4.28          | ((X0) = (k3_tarski @ X1))
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X0)
% 4.06/4.28          | ~ (r2_hidden @ X0 @ X1)
% 4.06/4.28          | ((X0) = (k3_tarski @ X1)))),
% 4.06/4.28      inference('sup-', [status(thm)], ['8', '9'])).
% 4.06/4.28  thf('11', plain,
% 4.06/4.28      (![X0 : $i, X1 : $i]:
% 4.06/4.28         (~ (r2_hidden @ X0 @ X1)
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X0)
% 4.06/4.28          | ((X0) = (k3_tarski @ X1))
% 4.06/4.28          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 4.06/4.28      inference('simplify', [status(thm)], ['10'])).
% 4.06/4.28  thf('12', plain,
% 4.06/4.28      (![X0 : $i, X1 : $i]:
% 4.06/4.28         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 4.06/4.28          | ((X0) = (k3_tarski @ X1))
% 4.06/4.28          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 4.06/4.28          | ((X0) = (k3_tarski @ X1))
% 4.06/4.28          | ~ (r2_hidden @ X0 @ X1))),
% 4.06/4.28      inference('sup-', [status(thm)], ['7', '11'])).
% 4.06/4.28  thf('13', plain,
% 4.06/4.28      (![X0 : $i, X1 : $i]:
% 4.06/4.28         (~ (r2_hidden @ X0 @ X1)
% 4.06/4.28          | ((X0) = (k3_tarski @ X1))
% 4.06/4.28          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 4.06/4.28      inference('simplify', [status(thm)], ['12'])).
% 4.06/4.28  thf('14', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         ((r2_hidden @ (sk_D @ X0 @ (k1_zfmisc_1 @ X0)) @ (k1_zfmisc_1 @ X0))
% 4.06/4.28          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.06/4.28      inference('sup-', [status(thm)], ['6', '13'])).
% 4.06/4.28  thf('15', plain,
% 4.06/4.28      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.06/4.28         (~ (r2_hidden @ X10 @ X9)
% 4.06/4.28          | (r1_tarski @ X10 @ X8)
% 4.06/4.28          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 4.06/4.28      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.06/4.28  thf('16', plain,
% 4.06/4.28      (![X8 : $i, X10 : $i]:
% 4.06/4.28         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 4.06/4.28      inference('simplify', [status(thm)], ['15'])).
% 4.06/4.28  thf('17', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | (r1_tarski @ (sk_D @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 4.06/4.28      inference('sup-', [status(thm)], ['14', '16'])).
% 4.06/4.28  thf(d3_tarski, axiom,
% 4.06/4.28    (![A:$i,B:$i]:
% 4.06/4.28     ( ( r1_tarski @ A @ B ) <=>
% 4.06/4.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.06/4.28  thf('18', plain,
% 4.06/4.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.06/4.28         (~ (r2_hidden @ X0 @ X1)
% 4.06/4.28          | (r2_hidden @ X0 @ X2)
% 4.06/4.28          | ~ (r1_tarski @ X1 @ X2))),
% 4.06/4.28      inference('cnf', [status(esa)], [d3_tarski])).
% 4.06/4.28  thf('19', plain,
% 4.06/4.28      (![X0 : $i, X1 : $i]:
% 4.06/4.28         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | (r2_hidden @ X1 @ X0)
% 4.06/4.28          | ~ (r2_hidden @ X1 @ (sk_D @ X0 @ (k1_zfmisc_1 @ X0))))),
% 4.06/4.28      inference('sup-', [status(thm)], ['17', '18'])).
% 4.06/4.28  thf('20', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         ((r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.06/4.28          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.06/4.28          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.06/4.28      inference('sup-', [status(thm)], ['1', '19'])).
% 4.06/4.28  thf('21', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 4.06/4.28      inference('simplify', [status(thm)], ['20'])).
% 4.06/4.28  thf('22', plain,
% 4.06/4.28      (![X13 : $i, X17 : $i, X18 : $i]:
% 4.06/4.28         (((X17) = (k3_tarski @ X13))
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X18)
% 4.06/4.28          | ~ (r2_hidden @ X18 @ X13)
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X17 @ X13) @ X17))),
% 4.06/4.28      inference('cnf', [status(esa)], [d4_tarski])).
% 4.06/4.28  thf('23', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.06/4.28          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))
% 4.06/4.28          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.06/4.28      inference('sup-', [status(thm)], ['21', '22'])).
% 4.06/4.28  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.06/4.28      inference('sup-', [status(thm)], ['3', '5'])).
% 4.06/4.28  thf('25', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.06/4.28          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.06/4.28      inference('demod', [status(thm)], ['23', '24'])).
% 4.06/4.28  thf('26', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         (~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)
% 4.06/4.28          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 4.06/4.28      inference('simplify', [status(thm)], ['25'])).
% 4.06/4.28  thf('27', plain,
% 4.06/4.28      (![X0 : $i]:
% 4.06/4.28         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 4.06/4.28          | (r2_hidden @ (sk_C_2 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 4.06/4.28      inference('simplify', [status(thm)], ['20'])).
% 4.06/4.28  thf('28', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 4.06/4.28      inference('clc', [status(thm)], ['26', '27'])).
% 4.06/4.28  thf('29', plain, (((sk_A) != (sk_A))),
% 4.06/4.28      inference('demod', [status(thm)], ['0', '28'])).
% 4.06/4.28  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 4.06/4.28  
% 4.06/4.28  % SZS output end Refutation
% 4.06/4.28  
% 4.06/4.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
